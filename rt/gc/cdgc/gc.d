/**
 * This module contains the garbage collector implementation.
 *
 * Copyright: Copyright (C) 2001-2007 Digital Mars, www.digitalmars.com.
 *            All rights reserved.
 * License:
 *  This software is provided 'as-is', without any express or implied
 *  warranty. In no event will the authors be held liable for any damages
 *  arising from the use of this software.
 *
 *  Permission is granted to anyone to use this software for any purpose,
 *  including commercial applications, and to alter it and redistribute it
 *  freely, in both source and binary form, subject to the following
 *  restrictions:
 *
 *  o  The origin of this software must not be misrepresented; you must not
 *     claim that you wrote the original software. If you use this software
 *     in a product, an acknowledgment in the product documentation would be
 *     appreciated but is not required.
 *  o  Altered source versions must be plainly marked as such, and must not
 *     be misrepresented as being the original software.
 *  o  This notice may not be removed or altered from any source
 *     distribution.
 * Authors:   Walter Bright, David Friedman, Sean Kelly
 */

module rt.gc.cdgc.gc;

// D Programming Language Garbage Collector implementation

/************** Debugging ***************************/

//debug = COLLECT_PRINTF;       // turn on printf's
//debug = MEMSTOMP;             // stomp on memory
//debug = SENTINEL;             // add underrun/overrrun protection
//debug = PTRCHECK;             // more pointer checking
//debug = PTRCHECK2;            // thorough but slow pointer checking

/*************** Configuration *********************/

version = STACKGROWSDOWN;       // growing the stack means subtracting from the stack pointer
                                // (use for Intel X86 CPUs)
                                // else growing the stack means adding to the stack pointer

/***************************************************/

import rt.gc.cdgc.bits: GCBits;
import rt.gc.cdgc.stats: GCStats;
import alloc = rt.gc.cdgc.alloc;

import cstdlib = tango.stdc.stdlib;
import cstring = tango.stdc.string;


version (GNU)
{
    // BUG: The following import will likely not work, since the gcc
    //      subdirectory is elsewhere.  Instead, perhaps the functions
    //      could be declared directly or some other resolution could
    //      be found.
    static import gcc.builtins; // for __builtin_unwind_int
}


struct BlkInfo
{
    void*  base;
    size_t size;
    uint   attr;
}

private
{
    enum BlkAttr : uint
    {
        FINALIZE = 0b0000_0001,
        NO_SCAN  = 0b0000_0010,
        NO_MOVE  = 0b0000_0100,
        ALL_BITS = 0b1111_1111
    }

    extern (C) void* rt_stackBottom();
    extern (C) void* rt_stackTop();

    extern (C) void rt_finalize( void* p, bool det = true );

    alias void delegate(Object) DEvent;
    extern (C) void rt_attachDisposeEvent(Object h, DEvent e);
    extern (C) bool rt_detachDisposeEvent(Object h, DEvent e);


    alias void delegate( void*, void* ) scanFn;

    extern (C) void rt_scanStaticData( scanFn scan );

    extern (C) bool thread_needLock();
    extern (C) void thread_suspendAll();
    extern (C) void thread_resumeAll();

    extern (C) void thread_scanAll( scanFn fn, void* curStackTop = null );

    extern (C) void onOutOfMemoryError();

    enum
    {
        OPFAIL = ~cast(size_t)0
    }
}


alias GC gc_t;


/* ============================ GC =============================== */


class GCLock { }                // just a dummy so we can get a global lock


const uint GCVERSION = 1;       // increment every time we change interface
                                // to GC.

class GC
{
    // For passing to debug code
    static size_t line;
    static char*  file;

    uint gcversion = GCVERSION;

    Gcx *gcx;                   // implementation
    static ClassInfo gcLock;    // global lock


    void initialize()
    {
        gcLock = GCLock.classinfo;
        gcx = cast(Gcx*) cstdlib.calloc(1, Gcx.sizeof);
        if (!gcx)
            onOutOfMemoryError();
        gcx.initialize();
        setStackBottom(rt_stackBottom());
    }


    void Dtor()
    {
        if (gcx)
        {
            gcx.Dtor();
            cstdlib.free(gcx);
            gcx = null;
        }
    }


    /**
     *
     */
    void enable()
    {
        if (!thread_needLock())
        {
            assert(gcx.disabled > 0);
            gcx.disabled--;
        }
        else synchronized (gcLock)
        {
            assert(gcx.disabled > 0);
            gcx.disabled--;
        }
    }


    /**
     *
     */
    void disable()
    {
        if (!thread_needLock())
        {
            gcx.disabled++;
        }
        else synchronized (gcLock)
        {
            gcx.disabled++;
        }
    }


    /**
     *
     */
    uint getAttr(void* p)
    {
        if (!p)
        {
            return 0;
        }

        uint go()
        {
            Pool* pool = gcx.findPool(p);
            uint  oldb = 0;

            if (pool)
            {
                auto biti = cast(size_t)(p - pool.baseAddr) / 16;

                oldb = gcx.getBits(pool, biti);
            }
            return oldb;
        }

        if (!thread_needLock())
        {
            return go();
        }
        else synchronized (gcLock)
        {
            return go();
        }
    }


    /**
     *
     */
    uint setAttr(void* p, uint mask)
    {
        if (!p)
        {
            return 0;
        }

        uint go()
        {
            Pool* pool = gcx.findPool(p);
            uint  oldb = 0;

            if (pool)
            {
                auto biti = cast(size_t)(p - pool.baseAddr) / 16;

                oldb = gcx.getBits(pool, biti);
                gcx.setBits(pool, biti, mask);
            }
            return oldb;
        }

        if (!thread_needLock())
        {
            return go();
        }
        else synchronized (gcLock)
        {
            return go();
        }
    }


    /**
     *
     */
    uint clrAttr(void* p, uint mask)
    {
        if (!p)
        {
            return 0;
        }

        uint go()
        {
            Pool* pool = gcx.findPool(p);
            uint  oldb = 0;

            if (pool)
            {
                auto biti = cast(size_t)(p - pool.baseAddr) / 16;

                oldb = gcx.getBits(pool, biti);
                gcx.clrBits(pool, biti, mask);
            }
            return oldb;
        }

        if (!thread_needLock())
        {
            return go();
        }
        else synchronized (gcLock)
        {
            return go();
        }
    }


    /**
     *
     */
    void *malloc(size_t size, uint bits = 0)
    {
        if (!size)
        {
            return null;
        }

        if (!thread_needLock())
        {
            return mallocNoSync(size, bits);
        }
        else synchronized (gcLock)
        {
            return mallocNoSync(size, bits);
        }
    }


    //
    //
    //
    private void *mallocNoSync(size_t size, uint bits = 0)
    {
        assert(size != 0);

        void *p = null;
        Bins bin;

        assert(gcx);

        size += SENTINEL_EXTRA;

        // Compute size bin
        // Cache previous binsize lookup - Dave Fladebo.
        static size_t lastsize = -1;
        static Bins lastbin;
        if (size == lastsize)
            bin = lastbin;
        else
        {
            bin = gcx.findBin(size);
            lastsize = size;
            lastbin = bin;
        }

        if (bin < B_PAGE)
        {
            p = gcx.bucket[bin];
            if (p is null)
            {
                if (!gcx.allocPage(bin) && !gcx.disabled)   // try to find a new page
                {
                    if (!thread_needLock())
                    {
                        /* Then we haven't locked it yet. Be sure
                         * and lock for a collection, since a finalizer
                         * may start a new thread.
                         */
                        synchronized (gcLock)
                        {
                            gcx.fullcollectshell();
                        }
                    }
                    else if (!gcx.fullcollectshell())       // collect to find a new page
                    {
                        //gcx.newPool(1);
                    }
                }
                if (!gcx.bucket[bin] && !gcx.allocPage(bin))
                {
                    gcx.newPool(1);         // allocate new pool to find a new page
                    int result = gcx.allocPage(bin);
                    if (!result)
                        onOutOfMemoryError();
                }
                p = gcx.bucket[bin];
            }

            // Return next item from free list
            gcx.bucket[bin] = (cast(List*)p).next;
            if( !(bits & BlkAttr.NO_SCAN) )
                cstring.memset(p + size, 0, binsize[bin] - size);
            debug (MEMSTOMP) cstring.memset(p, 0xF0, size);
        }
        else
        {
            p = gcx.bigAlloc(size);
            if (!p)
                onOutOfMemoryError();
        }
        size -= SENTINEL_EXTRA;
        p = sentinel_add(p);
        sentinel_init(p, size);

        if (bits)
        {
            Pool *pool = gcx.findPool(p);
            assert(pool);

            gcx.setBits(pool, cast(size_t)(p - pool.baseAddr) / 16, bits);
        }
        return p;
    }


    /**
     *
     */
    void *calloc(size_t size, uint bits = 0)
    {
        if (!size)
        {
            return null;
        }

        if (!thread_needLock())
        {
            return callocNoSync(size, bits);
        }
        else synchronized (gcLock)
        {
            return callocNoSync(size, bits);
        }
    }


    //
    //
    //
    private void *callocNoSync(size_t size, uint bits = 0)
    {
        assert(size != 0);

        void *p = mallocNoSync(size, bits);
        cstring.memset(p, 0, size);
        return p;
    }


    /**
     *
     */
    void *realloc(void *p, size_t size, uint bits = 0)
    {
        if (!thread_needLock())
        {
            return reallocNoSync(p, size, bits);
        }
        else synchronized (gcLock)
        {
            return reallocNoSync(p, size, bits);
        }
    }


    //
    //
    //
    private void *reallocNoSync(void *p, size_t size, uint bits = 0)
    {
        if (!size)
        {
            if (p)
            {
                freeNoSync(p);
                p = null;
            }
        }
        else if (!p)
        {
            p = mallocNoSync(size, bits);
        }
        else
        {
            void *p2;
            size_t psize;

            version (SENTINEL)
            {
                sentinel_Invariant(p);
                psize = *sentinel_size(p);
                if (psize != size)
                {
                    if (psize)
                    {
                        Pool *pool = gcx.findPool(p);

                        if (pool)
                        {
                            auto biti = cast(size_t)(p - pool.baseAddr) / 16;

                            if (bits)
                            {
                                gcx.clrBits(pool, biti, BlkAttr.ALL_BITS);
                                gcx.setBits(pool, biti, bits);
                            }
                            else
                            {
                                bits = gcx.getBits(pool, biti);
                            }
                        }
                    }
                    p2 = mallocNoSync(size, bits);
                    if (psize < size)
                        size = psize;
                    cstring.memcpy(p2, p, size);
                    p = p2;
                }
            }
            else
            {
                psize = gcx.findSize(p);        // find allocated size
                if (psize >= PAGESIZE && size >= PAGESIZE)
                {
                    auto psz = psize / PAGESIZE;
                    auto newsz = (size + PAGESIZE - 1) / PAGESIZE;
                    if (newsz == psz)
                        return p;

                    auto pool = gcx.findPool(p);
                    auto pagenum = (p - pool.baseAddr) / PAGESIZE;

                    if (newsz < psz)
                    {
                        // Shrink in place
                        synchronized (gcLock)
                        {
                            debug (MEMSTOMP)
                                cstring.memset(p + size, 0xF2, psize - size);
                            pool.freePages(pagenum + newsz, psz - newsz);
                        }
                        return p;
                    }
                    else if (pagenum + newsz <= pool.npages)
                    {
                        // Attempt to expand in place
                        synchronized (gcLock)
                        {
                            for (size_t i = pagenum + psz; 1;)
                            {
                                if (i == pagenum + newsz)
                                {
                                    debug (MEMSTOMP)
                                        cstring.memset(p + psize, 0xF0,
                                                size - psize);
                                    cstring.memset(pool.pagetable + pagenum +
                                            psz, B_PAGEPLUS, newsz - psz);
                                    return p;
                                }
                                if (i == pool.npages)
                                {
                                    break;
                                }
                                if (pool.pagetable[i] != B_FREE)
                                    break;
                                i++;
                            }
                        }
                    }
                }
                if (psize < size ||             // if new size is bigger
                    psize > size * 2)           // or less than half
                {
                    if (psize)
                    {
                        Pool *pool = gcx.findPool(p);

                        if (pool)
                        {
                            auto biti = cast(size_t)(p - pool.baseAddr) / 16;

                            if (bits)
                            {
                                gcx.clrBits(pool, biti, BlkAttr.ALL_BITS);
                                gcx.setBits(pool, biti, bits);
                            }
                            else
                            {
                                bits = gcx.getBits(pool, biti);
                            }
                        }
                    }
                    p2 = mallocNoSync(size, bits);
                    if (psize < size)
                        size = psize;
                    cstring.memcpy(p2, p, size);
                    p = p2;
                }
            }
        }
        return p;
    }


    /**
     * Attempt to in-place enlarge the memory block pointed to by p by at least
     * minbytes beyond its current capacity, up to a maximum of maxsize.  This
     * does not attempt to move the memory block (like realloc() does).
     *
     * Returns:
     *  0 if could not extend p,
     *  total size of entire memory block if successful.
     */
    size_t extend(void* p, size_t minsize, size_t maxsize)
    {
        if (!thread_needLock())
        {
            return extendNoSync(p, minsize, maxsize);
        }
        else synchronized (gcLock)
        {
            return extendNoSync(p, minsize, maxsize);
        }
    }


    //
    //
    //
    private size_t extendNoSync(void* p, size_t minsize, size_t maxsize)
    in
    {
        assert( minsize <= maxsize );
    }
    body
    {
        version (SENTINEL)
        {
            return 0;
        }
        auto psize = gcx.findSize(p);   // find allocated size
        if (psize < PAGESIZE)
            return 0;                   // cannot extend buckets

        auto psz = psize / PAGESIZE;
        auto minsz = (minsize + PAGESIZE - 1) / PAGESIZE;
        auto maxsz = (maxsize + PAGESIZE - 1) / PAGESIZE;

        auto pool = gcx.findPool(p);
        auto pagenum = (p - pool.baseAddr) / PAGESIZE;

        size_t sz;
        for (sz = 0; sz < maxsz; sz++)
        {
            auto i = pagenum + psz + sz;
            if (i == pool.npages)
                break;
            if (pool.pagetable[i] != B_FREE)
            {
                if (sz < minsz)
                    return 0;
                break;
            }
        }
        if (sz < minsz)
            return 0;
        debug (MEMSTOMP)
            cstring.memset(p + psize, 0xF0, (psz + sz) * PAGESIZE - psize);
        cstring.memset(pool.pagetable + pagenum + psz, B_PAGEPLUS, sz);
        gcx.p_cache = null;
        gcx.size_cache = 0;
        return (psz + sz) * PAGESIZE;
    }


    /**
     *
     */
    size_t reserve(size_t size)
    {
        if (!size)
        {
            return 0;
        }

        if (!thread_needLock())
        {
            return reserveNoSync(size);
        }
        else synchronized (gcLock)
        {
            return reserveNoSync(size);
        }
    }


    //
    //
    //
    private size_t reserveNoSync(size_t size)
    {
        assert(size != 0);
        assert(gcx);

        return gcx.reserve(size);
    }


    /**
     *
     */
    void free(void *p)
    {
        if (!p)
        {
            return;
        }

        if (!thread_needLock())
        {
            return freeNoSync(p);
        }
        else synchronized (gcLock)
        {
            return freeNoSync(p);
        }
    }


    //
    //
    //
    private void freeNoSync(void *p)
    {
        assert (p);

        Pool*  pool;
        size_t pagenum;
        Bins   bin;
        size_t biti;

        // Find which page it is in
        pool = gcx.findPool(p);
        if (!pool)                              // if not one of ours
            return;                             // ignore
        sentinel_Invariant(p);
        p = sentinel_sub(p);
        pagenum = cast(size_t)(p - pool.baseAddr) / PAGESIZE;
        biti = cast(size_t)(p - pool.baseAddr) / 16;
        gcx.clrBits(pool, biti, BlkAttr.ALL_BITS);

        bin = cast(Bins)pool.pagetable[pagenum];
        if (bin == B_PAGE)              // if large alloc
        {
            // Free pages
            size_t npages = 1;
            size_t n = pagenum;
            while (++n < pool.npages && pool.pagetable[n] == B_PAGEPLUS)
                npages++;
            debug (MEMSTOMP) cstring.memset(p, 0xF2, npages * PAGESIZE);
            pool.freePages(pagenum, npages);
        }
        else
        {
            // Add to free list
            List *list = cast(List*)p;

            debug (MEMSTOMP) cstring.memset(p, 0xF2, binsize[bin]);

            list.next = gcx.bucket[bin];
            gcx.bucket[bin] = list;
        }
    }


    /**
     * Determine the base address of the block containing p.  If p is not a gc
     * allocated pointer, return null.
     */
    void* addrOf(void *p)
    {
        if (!p)
        {
            return null;
        }

        if (!thread_needLock())
        {
            return addrOfNoSync(p);
        }
        else synchronized (gcLock)
        {
            return addrOfNoSync(p);
        }
    }


    //
    //
    //
    void* addrOfNoSync(void *p)
    {
        if (!p)
        {
            return null;
        }

        return gcx.findBase(p);
    }


    /**
     * Determine the allocated size of pointer p.  If p is an interior pointer
     * or not a gc allocated pointer, return 0.
     */
    size_t sizeOf(void *p)
    {
        if (!p)
        {
            return 0;
        }

        if (!thread_needLock())
        {
            return sizeOfNoSync(p);
        }
        else synchronized (gcLock)
        {
            return sizeOfNoSync(p);
        }
    }


    //
    //
    //
    private size_t sizeOfNoSync(void *p)
    {
        assert (p);

        version (SENTINEL)
        {
            p = sentinel_sub(p);
            size_t size = gcx.findSize(p);

            // Check for interior pointer
            // This depends on:
            // 1) size is a power of 2 for less than PAGESIZE values
            // 2) base of memory pool is aligned on PAGESIZE boundary
            if (cast(size_t)p & (size - 1) & (PAGESIZE - 1))
                size = 0;
            return size ? size - SENTINEL_EXTRA : 0;
        }
        else
        {
            if (p == gcx.p_cache)
                return gcx.size_cache;

            size_t size = gcx.findSize(p);

            // Check for interior pointer
            // This depends on:
            // 1) size is a power of 2 for less than PAGESIZE values
            // 2) base of memory pool is aligned on PAGESIZE boundary
            if (cast(size_t)p & (size - 1) & (PAGESIZE - 1))
                size = 0;
            else
            {
                gcx.p_cache = p;
                gcx.size_cache = size;
            }

            return size;
        }
    }


    /**
     * Determine the base address of the block containing p.  If p is not a gc
     * allocated pointer, return null.
     */
    BlkInfo query(void *p)
    {
        if (!p)
        {
            BlkInfo i;
            return  i;
        }

        if (!thread_needLock())
        {
            return queryNoSync(p);
        }
        else synchronized (gcLock)
        {
            return queryNoSync(p);
        }
    }


    //
    //
    //
    BlkInfo queryNoSync(void *p)
    {
        assert(p);

        return gcx.getInfo(p);
    }


    /**
     * Verify that pointer p:
     *  1) belongs to this memory pool
     *  2) points to the start of an allocated piece of memory
     *  3) is not on a free list
     */
    void check(void *p)
    {
        if (!p)
        {
            return;
        }

        if (!thread_needLock())
        {
            checkNoSync(p);
        }
        else synchronized (gcLock)
        {
            checkNoSync(p);
        }
    }


    //
    //
    //
    private void checkNoSync(void *p)
    {
        assert(p);

        sentinel_Invariant(p);
        debug (PTRCHECK)
        {
            Pool*  pool;
            size_t pagenum;
            Bins   bin;
            size_t size;

            p = sentinel_sub(p);
            pool = gcx.findPool(p);
            assert(pool);
            pagenum = cast(size_t)(p - pool.baseAddr) / PAGESIZE;
            bin = cast(Bins)pool.pagetable[pagenum];
            assert(bin <= B_PAGE);
            size = binsize[bin];
            assert((cast(size_t)p & (size - 1)) == 0);

            debug (PTRCHECK2)
            {
                if (bin < B_PAGE)
                {
                    // Check that p is not on a free list
                    List *list;

                    for (list = gcx.bucket[bin]; list; list = list.next)
                    {
                        assert(cast(void*)list != p);
                    }
                }
            }
        }
    }


    //
    //
    //
    private void setStackBottom(void *p)
    {
        version (STACKGROWSDOWN)
        {
            //p = (void *)((uint *)p + 4);
            if (p > gcx.stackBottom)
            {
                gcx.stackBottom = p;
            }
        }
        else
        {
            //p = (void *)((uint *)p - 4);
            if (p < gcx.stackBottom)
            {
                gcx.stackBottom = cast(char*)p;
            }
        }
    }


    /**
     * add p to list of roots
     */
    void addRoot(void *p)
    {
        if (!p)
        {
            return;
        }

        if (!thread_needLock())
        {
            gcx.addRoot(p);
        }
        else synchronized (gcLock)
        {
            gcx.addRoot(p);
        }
    }


    /**
     * remove p from list of roots
     */
    void removeRoot(void *p)
    {
        if (!p)
        {
            return;
        }

        if (!thread_needLock())
        {
            gcx.removeRoot(p);
        }
        else synchronized (gcLock)
        {
            gcx.removeRoot(p);
        }
    }


    /**
     * add range to scan for roots
     */
    void addRange(void *p, size_t sz)
    {
        if (!p || !sz)
        {
            return;
        }

        if (!thread_needLock())
        {
            gcx.addRange(p, p + sz);
        }
        else synchronized (gcLock)
        {
            gcx.addRange(p, p + sz);
        }
    }


    /**
     * remove range
     */
    void removeRange(void *p)
    {
        if (!p)
        {
            return;
        }

        if (!thread_needLock())
        {
            gcx.removeRange(p);
        }
        else synchronized (gcLock)
        {
            gcx.removeRange(p);
        }
    }


    /**
     * do full garbage collection
     */
    void fullCollect()
    {

        if (!thread_needLock())
        {
            gcx.fullcollectshell();
        }
        else synchronized (gcLock)
        {
            gcx.fullcollectshell();
        }

        version (none)
        {
            GCStats stats;
            getStats(stats);
        }

    }


    /**
     * do full garbage collection ignoring roots
     */
    void fullCollectNoStack()
    {
        if (!thread_needLock())
        {
            gcx.noStack++;
            gcx.fullcollectshell();
            gcx.noStack--;
        }
        else synchronized (gcLock)
        {
            gcx.noStack++;
            gcx.fullcollectshell();
            gcx.noStack--;
        }
    }


    /**
     * minimize free space usage
     */
    void minimize()
    {
        if (!thread_needLock())
        {
            gcx.minimize();
        }
        else synchronized (gcLock)
        {
            gcx.minimize();
        }
    }


    /**
     * Retrieve statistics about garbage collection.
     * Useful for debugging and tuning.
     */
    void getStats(out GCStats stats)
    {
        if (!thread_needLock())
        {
            getStatsNoSync(stats);
        }
        else synchronized (gcLock)
        {
            getStatsNoSync(stats);
        }
    }


    //
    //
    //
    private void getStatsNoSync(out GCStats stats)
    {
        size_t psize = 0;
        size_t usize = 0;
        size_t flsize = 0;

        size_t n;
        size_t bsize = 0;

        cstring.memset(&stats, 0, GCStats.sizeof);

        for (n = 0; n < gcx.npools; n++)
        {
            Pool *pool = gcx.pooltable[n];
            psize += pool.npages * PAGESIZE;
            for (size_t j = 0; j < pool.npages; j++)
            {
                Bins bin = cast(Bins)pool.pagetable[j];
                if (bin == B_FREE)
                    stats.freeblocks++;
                else if (bin == B_PAGE)
                    stats.pageblocks++;
                else if (bin < B_PAGE)
                    bsize += PAGESIZE;
            }
        }

        for (n = 0; n < B_PAGE; n++)
        {
            for (List *list = gcx.bucket[n]; list; list = list.next)
                flsize += binsize[n];
        }

        usize = bsize - flsize;

        stats.poolsize = psize;
        stats.usedsize = bsize - flsize;
        stats.freelistsize = flsize;
    }

    /******************* weak-reference support *********************/

    // call locked if necessary
    private T locked(T)(in T delegate() code)
    {
        if (thread_needLock)
            synchronized(gcLock) return code();
        else
           return code();
    }

    private struct WeakPointer
    {
        Object reference;

        void ondestroy(Object r)
        {
            assert(r is reference);
            // lock for memory consistency (parallel readers)
            // also ensures that weakpointerDestroy can be called while another
            // thread is freeing the reference with "delete"
            locked!(void)({ reference = null; });
        }
    }

    /**
     * Create a weak pointer to the given object.
     * Returns a pointer to an opaque struct allocated in C memory.
     */
    void* weakpointerCreate( Object r )
    {
        if (r)
	{
            // must be allocated in C memory
            // 1. to hide the reference from the GC
            // 2. the GC doesn't scan delegates added by rt_attachDisposeEvent
            //    for references
            auto wp = cast(WeakPointer*)(cstdlib.malloc(WeakPointer.sizeof));
            if (!wp)
                onOutOfMemoryError();
            wp.reference = r;
            rt_attachDisposeEvent(r, &wp.ondestroy);
            return wp;
        }
        return null;
    }

    /**
     * Destroy a weak pointer returned by weakpointerCreate().
     * If null is passed, nothing happens.
     */
    void weakpointerDestroy( void* p )
    {
        if (p)
	{
            auto wp = cast(WeakPointer*)p;
            // must be extra careful about the GC or parallel threads
            // finalizing the reference at the same time
            locked!(void)({
                   if (wp.reference)
                       rt_detachDisposeEvent(wp.reference, &wp.ondestroy);
                  });
            cstdlib.free(wp);
        }
    }

    /**
     * Query a weak pointer and return either the object passed to
     * weakpointerCreate, or null if it was free'd in the meantime.
     * If null is passed, null is returned.
     */
    Object weakpointerGet( void* p )
    {
        if (p)
	{
            // NOTE: could avoid the lock by using Fawzi style GC counters but
            // that'd require core.sync.Atomic and lots of care about memory
            // consistency it's an optional optimization see
            // http://dsource.org/projects/tango/browser/trunk/user/tango/core/Lifetime.d?rev=5100#L158
            return locked!(Object)({
                  return (cast(WeakPointer*)p).reference;
                  });
            }
    }
}


/* ============================ Gcx =============================== */

enum
{
    PAGESIZE =    4096,
    POOLSIZE =   (4096*256),
}


enum
{
    B_16,
    B_32,
    B_64,
    B_128,
    B_256,
    B_512,
    B_1024,
    B_2048,
    B_PAGE,             // start of large alloc
    B_PAGEPLUS,         // continuation of large alloc
    B_FREE,             // free page
    B_MAX
}


alias ubyte Bins;


struct List
{
    List *next;
}


struct Range
{
    void *pbot;
    void *ptop;
}


const uint binsize[B_MAX] = [ 16,32,64,128,256,512,1024,2048,4096 ];
const uint notbinsize[B_MAX] = [ ~(16u-1),~(32u-1),~(64u-1),~(128u-1),~(256u-1),
                                ~(512u-1),~(1024u-1),~(2048u-1),~(4096u-1) ];

/* ============================ Gcx =============================== */


struct Gcx
{

    void *p_cache;
    size_t size_cache;

    size_t nroots;
    size_t rootdim;
    void **roots;

    size_t nranges;
    size_t rangedim;
    Range *ranges;

    uint noStack;       // !=0 means don't scan stack
    uint log;           // turn on logging
    uint anychanges;
    void *stackBottom;
    uint inited;
    int disabled;       // turn off collections if >0

    byte *minAddr;      // min(baseAddr)
    byte *maxAddr;      // max(topAddr)

    size_t npools;
    Pool **pooltable;

    List *bucket[B_MAX];        // free list for each size


    void initialize()
    {
        int dummy;
        (cast(byte*)this)[0 .. Gcx.sizeof] = 0;
        stackBottom = cast(char*)&dummy;
        //printf("gcx = %p, self = %x\n", this, self);
        inited = 1;
    }


    void Dtor()
    {
        inited = 0;

        for (size_t i = 0; i < npools; i++)
        {
            Pool *pool = pooltable[i];
            pool.Dtor();
            cstdlib.free(pool);
        }

        // Even when free() can be called with a null pointer, the extra call
        // might be significant. On hard GC benchmarks making the test for null
        // here (i.e. not making the call) can reduce the GC time by almost
        // ~5%.
        if (pooltable)
            cstdlib.free(pooltable);
        if (roots)
            cstdlib.free(roots);
        if (ranges)
            cstdlib.free(ranges);
    }


    void Invariant() { }


    invariant
    {
        if (inited)
        {
        //printf("Gcx.invariant(): this = %p\n", this);
            size_t i;

            for (i = 0; i < npools; i++)
            {
                Pool *pool = pooltable[i];
                pool.Invariant();
                if (i == 0)
                {
                    assert(minAddr == pool.baseAddr);
                }
                if (i + 1 < npools)
                {
                    assert(pool.opCmp(pooltable[i + 1]) < 0);
                }
                else if (i + 1 == npools)
                {
                    assert(maxAddr == pool.topAddr);
                }
            }

            if (roots)
            {
                assert(rootdim != 0);
                assert(nroots <= rootdim);
            }

            if (ranges)
            {
                assert(rangedim != 0);
                assert(nranges <= rangedim);

                for (i = 0; i < nranges; i++)
                {
                    assert(ranges[i].pbot);
                    assert(ranges[i].ptop);
                    assert(ranges[i].pbot <= ranges[i].ptop);
                }
            }

            for (i = 0; i < B_PAGE; i++)
            {
                for (List *list = bucket[i]; list; list = list.next)
                {
                }
            }
        }
    }


    /**
     *
     */
    void addRoot(void *p)
    {
        if (nroots == rootdim)
        {
            size_t newdim = rootdim * 2 + 16;
            void** newroots;

            newroots = cast(void**) cstdlib.malloc(newdim * newroots[0].sizeof);
            if (!newroots)
                onOutOfMemoryError();
            if (roots)
            {
                cstring.memcpy(newroots, roots, nroots * newroots[0].sizeof);
                cstdlib.free(roots);
            }
            roots = newroots;
            rootdim = newdim;
        }
        roots[nroots] = p;
        nroots++;
    }


    /**
     *
     */
    void removeRoot(void *p)
    {
        for (size_t i = nroots; i--;)
        {
            if (roots[i] == p)
            {
                nroots--;
                cstring.memmove(roots + i, roots + i + 1,
                        (nroots - i) * roots[0].sizeof);
                return;
            }
        }
        assert(0);
    }


    /**
     *
     */
    void addRange(void *pbot, void *ptop)
    {
        if (nranges == rangedim)
        {
            size_t newdim = rangedim * 2 + 16;
            Range *newranges;

            newranges = cast(Range*) cstdlib.malloc(newdim * Range.sizeof);
            if (!newranges)
                onOutOfMemoryError();
            if (ranges)
            {
                cstring.memcpy(newranges, ranges, nranges * Range.sizeof);
                cstdlib.free(ranges);
            }
            ranges = newranges;
            rangedim = newdim;
        }
        ranges[nranges].pbot = pbot;
        ranges[nranges].ptop = ptop;
        nranges++;
    }


    /**
     *
     */
    void removeRange(void *pbot)
    {
        for (size_t i = nranges; i--;)
        {
            if (ranges[i].pbot == pbot)
            {
                nranges--;
                cstring.memmove(ranges + i, ranges + i + 1,
                        (nranges - i) * ranges[0].sizeof);
                return;
            }
        }

        // This is a fatal error, but ignore it.
        // The problem is that we can get a Close() call on a thread
        // other than the one the range was allocated on.
        //assert(zero);
    }


    /**
     * Find Pool that pointer is in.
     * Return null if not in a Pool.
     * Assume pooltable[] is sorted.
     */
    Pool *findPool(void *p)
    {
        if (p >= minAddr && p < maxAddr)
        {
            if (npools == 1)
            {
                return pooltable[0];
            }

            for (size_t i = 0; i < npools; i++)
            {
                Pool *pool;

                pool = pooltable[i];
                if (p < pool.topAddr)
                {
                    if (pool.baseAddr <= p)
                        return pool;
                    break;
                }
            }
        }
        return null;
    }


    /**
     * Find base address of block containing pointer p.
     * Returns null if not a gc'd pointer
     */
    void* findBase(void *p)
    {
        Pool *pool;

        pool = findPool(p);
        if (pool)
        {
            size_t offset = cast(size_t)(p - pool.baseAddr);
            size_t pn = offset / PAGESIZE;
            Bins   bin = cast(Bins)pool.pagetable[pn];

            // Adjust bit to be at start of allocated memory block
            if (bin <= B_PAGE)
            {
                return pool.baseAddr + (offset & notbinsize[bin]);
            }
            else if (bin == B_PAGEPLUS)
            {
                do
                {
                    --pn, offset -= PAGESIZE;
                } while (cast(Bins)pool.pagetable[pn] == B_PAGEPLUS);

                return pool.baseAddr + (offset & (offset.max ^ (PAGESIZE-1)));
            }
            else
            {
                // we are in a B_FREE page
                return null;
            }
        }
        return null;
    }


    /**
     * Find size of pointer p.
     * Returns 0 if not a gc'd pointer
     */
    size_t findSize(void *p)
    {
        Pool*  pool;
        size_t size = 0;

        pool = findPool(p);
        if (pool)
        {
            size_t pagenum;
            Bins   bin;

            pagenum = cast(size_t)(p - pool.baseAddr) / PAGESIZE;
            bin = cast(Bins)pool.pagetable[pagenum];
            size = binsize[bin];
            if (bin == B_PAGE)
            {
                ubyte* pt;
                size_t i;

                pt = &pool.pagetable[0];
                for (i = pagenum + 1; i < pool.npages; i++)
                {
                    if (pt[i] != B_PAGEPLUS)
                        break;
                }
                size = (i - pagenum) * PAGESIZE;
            }
        }
        return size;
    }


    /**
     *
     */
    BlkInfo getInfo(void* p)
    {
        Pool*   pool;
        BlkInfo info;

        pool = findPool(p);
        if (pool)
        {
            size_t offset = cast(size_t)(p - pool.baseAddr);
            size_t pn = offset / PAGESIZE;
            Bins   bin = cast(Bins)pool.pagetable[pn];

            ////////////////////////////////////////////////////////////////////
            // findAddr
            ////////////////////////////////////////////////////////////////////

            if (bin <= B_PAGE)
            {
                info.base = pool.baseAddr + (offset & notbinsize[bin]);
            }
            else if (bin == B_PAGEPLUS)
            {
                do
                {
                    --pn, offset -= PAGESIZE;
                }
                while (cast(Bins)pool.pagetable[pn] == B_PAGEPLUS);

                info.base = pool.baseAddr + (offset & (offset.max ^ (PAGESIZE-1)));

                // fix bin for use by size calc below
                bin = cast(Bins)pool.pagetable[pn];
            }

            ////////////////////////////////////////////////////////////////////
            // findSize
            ////////////////////////////////////////////////////////////////////

            info.size = binsize[bin];
            if (bin == B_PAGE)
            {
                ubyte* pt;
                size_t i;

                pt = &pool.pagetable[0];
                for (i = pn + 1; i < pool.npages; i++)
                {
                    if (pt[i] != B_PAGEPLUS)
                        break;
                }
                info.size = (i - pn) * PAGESIZE;
            }

            ////////////////////////////////////////////////////////////////////
            // getBits
            ////////////////////////////////////////////////////////////////////

            info.attr = getBits(pool, cast(size_t)(offset / 16));
        }
        return info;
    }


    /**
     * Compute bin for size.
     */
    static Bins findBin(size_t size)
    {
        Bins bin;
        if (size <= 256)
        {
            if (size <= 64)
            {
                if (size <= 16)
                    bin = B_16;
                else if (size <= 32)
                    bin = B_32;
                else
                    bin = B_64;
            }
            else
            {
                if (size <= 128)
                    bin = B_128;
                else
                    bin = B_256;
            }
        }
        else
        {
            if (size <= 1024)
            {
                if (size <= 512)
                    bin = B_512;
                else
                    bin = B_1024;
            }
            else
            {
                if (size <= 2048)
                    bin = B_2048;
                else
                    bin = B_PAGE;
            }
        }
        return bin;
    }


    /**
     * Allocate a new pool of at least size bytes.
     * Sort it into pooltable[].
     * Mark all memory in the pool as B_FREE.
     * Return the actual number of bytes reserved or 0 on error.
     */
    size_t reserve(size_t size)
    {
        size_t npages = (size + PAGESIZE - 1) / PAGESIZE;
        Pool*  pool = newPool(npages);

        if (!pool)
            return 0;
        return pool.npages * PAGESIZE;
    }


    /**
     * Minimizes physical memory usage by returning free pools to the OS.
     */
    void minimize()
    {
        size_t n;
        size_t pn;
        Pool*  pool;

        for (n = 0; n < npools; n++)
        {
            pool = pooltable[n];
            for (pn = 0; pn < pool.npages; pn++)
            {
                if (cast(Bins)pool.pagetable[pn] != B_FREE)
                    break;
            }
            if (pn < pool.npages)
            {
                n++;
                continue;
            }
            pool.Dtor();
            cstdlib.free(pool);
            cstring.memmove(pooltable + n,
                            pooltable + n + 1,
                            (--npools - n) * (Pool*).sizeof);
            minAddr = pooltable[0].baseAddr;
            maxAddr = pooltable[npools - 1].topAddr;
        }
    }


    /**
     * Allocate a chunk of memory that is larger than a page.
     * Return null if out of memory.
     */
    void *bigAlloc(size_t size)
    {
        Pool*  pool;
        size_t npages;
        size_t n;
        size_t pn;
        size_t freedpages;
        void*  p;
        int    state;

        npages = (size + PAGESIZE - 1) / PAGESIZE;

        for (state = 0; ; )
        {
            // This code could use some refinement when repeatedly
            // allocating very large arrays.

            for (n = 0; n < npools; n++)
            {
                pool = pooltable[n];
                pn = pool.allocPages(npages);
                if (pn != OPFAIL)
                    goto L1;
            }

            // Failed
            switch (state)
            {
            case 0:
                if (disabled)
                {
                    state = 1;
                    continue;
                }
                // Try collecting
                freedpages = fullcollectshell();
                if (freedpages >= npools * ((POOLSIZE / PAGESIZE) / 4))
                {
                    state = 1;
                    continue;
                }
                // Release empty pools to prevent bloat
                minimize();
                // Allocate new pool
                pool = newPool(npages);
                if (!pool)
                {
                    state = 2;
                    continue;
                }
                pn = pool.allocPages(npages);
                assert(pn != OPFAIL);
                goto L1;
            case 1:
                // Release empty pools to prevent bloat
                minimize();
                // Allocate new pool
                pool = newPool(npages);
                if (!pool)
                    goto Lnomemory;
                pn = pool.allocPages(npages);
                assert(pn != OPFAIL);
                goto L1;
            case 2:
                goto Lnomemory;
            default:
                assert(false);
            }
        }

      L1:
        pool.pagetable[pn] = B_PAGE;
        if (npages > 1)
            cstring.memset(&pool.pagetable[pn + 1], B_PAGEPLUS, npages - 1);
        p = pool.baseAddr + pn * PAGESIZE;
        cstring.memset(cast(char *)p + size, 0, npages * PAGESIZE - size);
        debug (MEMSTOMP) cstring.memset(p, 0xF1, size);
        return p;

      Lnomemory:
        return null; // let mallocNoSync handle the error
    }


    /**
     * Allocate a new pool with at least npages in it.
     * Sort it into pooltable[].
     * Return null if failed.
     */
    Pool *newPool(size_t npages)
    {
        Pool*  pool;
        Pool** newpooltable;
        size_t newnpools;
        size_t i;

        // Minimum of POOLSIZE
        if (npages < POOLSIZE/PAGESIZE)
            npages = POOLSIZE/PAGESIZE;
        else if (npages > POOLSIZE/PAGESIZE)
        {
            // Give us 150% of requested size, so there's room to extend
            auto n = npages + (npages >> 1);
            if (n < size_t.max/PAGESIZE)
                npages = n;
        }

        // Allocate successively larger pools up to 8 megs
        if (npools)
        {
            size_t n = npools;
            if (n > 8)
                n = 8;                  // cap pool size at 8 megs
            n *= (POOLSIZE / PAGESIZE);
            if (npages < n)
                npages = n;
        }

        pool = cast(Pool *) cstdlib.calloc(1, Pool.sizeof);
        if (pool)
        {
            pool.initialize(npages);
            if (!pool.baseAddr)
                goto Lerr;

            newnpools = npools + 1;
            newpooltable = cast(Pool **) cstdlib.realloc(pooltable,
                    newnpools * (Pool *).sizeof);
            if (!newpooltable)
                goto Lerr;

            // Sort pool into newpooltable[]
            for (i = 0; i < npools; i++)
            {
                if (pool.opCmp(newpooltable[i]) < 0)
                     break;
            }
            cstring.memmove(newpooltable + i + 1, newpooltable + i,
                    (npools - i) * (Pool *).sizeof);
            newpooltable[i] = pool;

            pooltable = newpooltable;
            npools = newnpools;

            minAddr = pooltable[0].baseAddr;
            maxAddr = pooltable[npools - 1].topAddr;
        }
        return pool;

      Lerr:
        pool.Dtor();
        cstdlib.free(pool);
        return null;
    }


    /**
     * Allocate a page of bin's.
     * Returns:
     *  0       failed
     */
    int allocPage(Bins bin)
    {
        Pool*  pool;
        size_t n;
        size_t pn;
        byte*  p;
        byte*  ptop;

        for (n = 0; n < npools; n++)
        {
            pool = pooltable[n];
            pn = pool.allocPages(1);
            if (pn != OPFAIL)
                goto L1;
        }
        return 0;               // failed

      L1:
        pool.pagetable[pn] = cast(ubyte)bin;

        // Convert page to free list
        size_t size = binsize[bin];
        List **b = &bucket[bin];

        p = pool.baseAddr + pn * PAGESIZE;
        ptop = p + PAGESIZE;
        for (; p < ptop; p += size)
        {
            (cast(List *)p).next = *b;
            *b = cast(List *)p;
        }
        return 1;
    }


    /**
     * Search a range of memory values and mark any pointers into the GC pool.
     */
    void mark(void *pbot, void *ptop)
    {
        void **p1 = cast(void **)pbot;
        void **p2 = cast(void **)ptop;
        size_t pcache = 0;
        uint changes = 0;

        //printf("marking range: %p -> %p\n", pbot, ptop);
        for (; p1 < p2; p1++)
        {
            Pool *pool;
            byte *p = cast(byte *)(*p1);

            if (p >= minAddr && p < maxAddr)
            {
                if ((cast(size_t)p & ~(PAGESIZE-1)) == pcache)
                    continue;

                pool = findPool(p);
                if (pool)
                {
                    size_t offset = cast(size_t)(p - pool.baseAddr);
                    size_t biti;
                    size_t pn = offset / PAGESIZE;
                    Bins   bin = cast(Bins)pool.pagetable[pn];

                    // Adjust bit to be at start of allocated memory block
                    if (bin <= B_PAGE)
                        biti = (offset & notbinsize[bin]) >> 4;
                    else if (bin == B_PAGEPLUS)
                    {
                        do
                        {
                            --pn;
                        }
                        while (cast(Bins)pool.pagetable[pn] == B_PAGEPLUS);
                        biti = pn * (PAGESIZE / 16);
                    }
                    else
                    {
                        // Don't mark bits in B_FREE pages
                        continue;
                    }

                    if (bin >= B_PAGE) // Cache B_PAGE and B_PAGEPLUS lookups
                        pcache = cast(size_t)p & ~(PAGESIZE-1);

                    if (!pool.mark.test(biti))
                    {
                        pool.mark.set(biti);
                        if (!pool.noscan.test(biti))
                        {
                            pool.scan.set(biti);
                            changes = 1;
                        }
                    }
                }
            }
        }
        anychanges |= changes;
    }


    /**
     * Return number of full pages free'd.
     */
    size_t fullcollectshell()
    {
        // The purpose of the 'shell' is to ensure all the registers
        // get put on the stack so they'll be scanned
        void *sp;
        size_t result;
        version (GNU)
        {
            gcc.builtins.__builtin_unwind_init();
            sp = & sp;
        }
        else version(LDC)
        {
            version(X86)
            {
                uint eax,ecx,edx,ebx,ebp,esi,edi;
                asm
                {
                    mov eax[EBP], EAX      ;
                    mov ecx[EBP], ECX      ;
                    mov edx[EBP], EDX      ;
                    mov ebx[EBP], EBX      ;
                    mov ebp[EBP], EBP      ;
                    mov esi[EBP], ESI      ;
                    mov edi[EBP], EDI      ;
                    mov  sp[EBP], ESP      ;
                }
            }
            else version (X86_64)
            {
                ulong rax,rbx,rcx,rdx,rbp,rsi,rdi,r8,r9,r10,r11,r12,r13,r14,r15;
                asm
                {
                    movq rax[RBP], RAX      ;
                    movq rbx[RBP], RBX      ;
                    movq rcx[RBP], RCX      ;
                    movq rdx[RBP], RDX      ;
                    movq rbp[RBP], RBP      ;
                    movq rsi[RBP], RSI      ;
                    movq rdi[RBP], RDI      ;
                    movq r8 [RBP], R8       ;
                    movq r9 [RBP], R9       ;
                    movq r10[RBP], R10      ;
                    movq r11[RBP], R11      ;
                    movq r12[RBP], R12      ;
                    movq r13[RBP], R13      ;
                    movq r14[RBP], R14      ;
                    movq r15[RBP], R15      ;
                    movq  sp[RBP], RSP      ;
                }
            }
            else
            {
                static assert( false, "Architecture not supported." );
            }
        }
        else
        {
        asm
        {
            pushad              ;
            mov sp[EBP],ESP     ;
        }
        }
        result = fullcollect(sp);
        version (GNU)
        {
            // nothing to do
        }
        else version(LDC)
        {
            // nothing to do
        }
        else
        {
        asm
        {
            popad               ;
        }
        }
        return result;
    }


    /**
     *
     */
    size_t fullcollect(void *stackTop)
    {
        size_t n;
        Pool*  pool;

        debug(COLLECT_PRINTF) printf("Gcx.fullcollect()\n");

        thread_suspendAll();

        p_cache = null;
        size_cache = 0;

        anychanges = 0;
        for (n = 0; n < npools; n++)
        {
            pool = pooltable[n];
            pool.mark.zero();
            pool.scan.zero();
            pool.freebits.zero();
        }

        // Mark each free entry, so it doesn't get scanned
        for (n = 0; n < B_PAGE; n++)
        {
            for (List *list = bucket[n]; list; list = list.next)
            {
                pool = findPool(list);
                assert(pool);
                pool.freebits.set(cast(size_t)(cast(byte*)list - pool.baseAddr) / 16);
            }
        }

        for (n = 0; n < npools; n++)
        {
            pool = pooltable[n];
            pool.mark.copy(&pool.freebits);
        }

        rt_scanStaticData( &mark );

        if (!noStack)
        {
            // Scan stacks and registers for each paused thread
            thread_scanAll( &mark, stackTop );
        }

        // Scan roots[]
        debug(COLLECT_PRINTF) printf("scan roots[]\n");
        mark(roots, roots + nroots);

        // Scan ranges[]
        debug(COLLECT_PRINTF) printf("scan ranges[]\n");
        //log++;
        for (n = 0; n < nranges; n++)
        {
            debug(COLLECT_PRINTF) printf("\t%x .. %x\n", ranges[n].pbot, ranges[n].ptop);
            mark(ranges[n].pbot, ranges[n].ptop);
        }
        //log--;

        debug(COLLECT_PRINTF) printf("\tscan heap\n");
        while (anychanges)
        {
            anychanges = 0;
            for (n = 0; n < npools; n++)
            {
                uint *bbase;
                uint *b;
                uint *btop;

                pool = pooltable[n];

                bbase = pool.scan.base();
                btop = bbase + pool.scan.nwords;
                for (b = bbase; b < btop;)
                {
                    Bins   bin;
                    size_t pn;
                    size_t u;
                    size_t bitm;
                    byte*  o;

                    bitm = *b;
                    if (!bitm)
                    {
                        b++;
                        continue;
                    }
                    *b = 0;

                    o = pool.baseAddr + (b - bbase) * 32 * 16;
                    if (!(bitm & 0xFFFF))
                    {
                        bitm >>= 16;
                        o += 16 * 16;
                    }
                    for (; bitm; o += 16, bitm >>= 1)
                    {
                        if (!(bitm & 1))
                            continue;

                        pn = cast(size_t)(o - pool.baseAddr) / PAGESIZE;
                        bin = cast(Bins)pool.pagetable[pn];
                        if (bin < B_PAGE)
                        {
                            mark(o, o + binsize[bin]);
                        }
                        else if (bin == B_PAGE || bin == B_PAGEPLUS)
                        {
                            if (bin == B_PAGEPLUS)
                            {
                                while (pool.pagetable[pn - 1] != B_PAGE)
                                    pn--;
                            }
                            u = 1;
                            while (pn + u < pool.npages && pool.pagetable[pn + u] == B_PAGEPLUS)
                                u++;
                            mark(o, o + u * PAGESIZE);
                        }
                    }
                }
            }
        }

        thread_resumeAll();

        // Free up everything not marked
        debug(COLLECT_PRINTF) printf("\tfree'ing\n");
        size_t freedpages = 0;
        size_t freed = 0;
        for (n = 0; n < npools; n++)
        {
            pool = pooltable[n];
            uint*  bbase = pool.mark.base();
            size_t pn;
            for (pn = 0; pn < pool.npages; pn++, bbase += PAGESIZE / (32 * 16))
            {
                Bins bin = cast(Bins)pool.pagetable[pn];

                if (bin < B_PAGE)
                {
                    auto size = binsize[bin];
                    byte* p = pool.baseAddr + pn * PAGESIZE;
                    byte* ptop = p + PAGESIZE;
                    size_t biti = pn * (PAGESIZE/16);
                    size_t bitstride = size / 16;

    version(none) // BUG: doesn't work because freebits() must also be cleared
    {
                    // If free'd entire page
                    if (bbase[0] == 0 && bbase[1] == 0 && bbase[2] == 0 && bbase[3] == 0 &&
                        bbase[4] == 0 && bbase[5] == 0 && bbase[6] == 0 && bbase[7] == 0)
                    {
                        for (; p < ptop; p += size, biti += bitstride)
                        {
                            if (pool.finals.nbits && pool.finals.testClear(biti))
                                rt_finalize(cast(List *)sentinel_add(p), false/*noStack > 0*/);
                            gcx.clrBits(pool, biti, BlkAttr.ALL_BITS);

                            List *list = cast(List *)p;

                            debug (MEMSTOMP) cstring.memset(p, 0xF3, size);
                        }
                        pool.pagetable[pn] = B_FREE;
                        freed += PAGESIZE;
                        continue;
                    }
    }
                    for (; p < ptop; p += size, biti += bitstride)
                    {
                        if (!pool.mark.test(biti))
                        {
                            sentinel_Invariant(sentinel_add(p));

                            pool.freebits.set(biti);
                            if (pool.finals.nbits && pool.finals.testClear(biti))
                                rt_finalize(cast(List *)sentinel_add(p), false/*noStack > 0*/);
                            clrBits(pool, biti, BlkAttr.ALL_BITS);

                            List *list = cast(List *)p;

                            debug (MEMSTOMP) cstring.memset(p, 0xF3, size);

                            freed += size;
                        }
                    }
                }
                else if (bin == B_PAGE)
                {
                    size_t biti = pn * (PAGESIZE / 16);
                    if (!pool.mark.test(biti))
                    {
                        byte *p = pool.baseAddr + pn * PAGESIZE;
                        sentinel_Invariant(sentinel_add(p));
                        if (pool.finals.nbits && pool.finals.testClear(biti))
                            rt_finalize(sentinel_add(p), false/*noStack > 0*/);
                        clrBits(pool, biti, BlkAttr.ALL_BITS);

                        debug(COLLECT_PRINTF) printf("\tcollecting big %x\n", p);
                        pool.pagetable[pn] = B_FREE;
                        freedpages++;
                        debug (MEMSTOMP) cstring.memset(p, 0xF3, PAGESIZE);
                        while (pn + 1 < pool.npages && pool.pagetable[pn + 1] == B_PAGEPLUS)
                        {
                            pn++;
                            pool.pagetable[pn] = B_FREE;
                            freedpages++;

                            debug (MEMSTOMP)
                            {
                                p += PAGESIZE;
                                cstring.memset(p, 0xF3, PAGESIZE);
                            }
                        }
                    }
                }
            }
        }

        // Zero buckets
        bucket[] = null;

        // Free complete pages, rebuild free list
        debug(COLLECT_PRINTF) printf("\tfree complete pages\n");
        size_t recoveredpages = 0;
        for (n = 0; n < npools; n++)
        {
            pool = pooltable[n];
            for (size_t pn = 0; pn < pool.npages; pn++)
            {
                Bins   bin = cast(Bins)pool.pagetable[pn];
                size_t biti;
                size_t u;

                if (bin < B_PAGE)
                {
                    size_t size = binsize[bin];
                    size_t bitstride = size / 16;
                    size_t bitbase = pn * (PAGESIZE / 16);
                    size_t bittop = bitbase + (PAGESIZE / 16);
                    byte*  p;

                    biti = bitbase;
                    for (biti = bitbase; biti < bittop; biti += bitstride)
                    {
                        if (!pool.freebits.test(biti))
                            goto Lnotfree;
                    }
                    pool.pagetable[pn] = B_FREE;
                    recoveredpages++;
                    continue;

                 Lnotfree:
                    p = pool.baseAddr + pn * PAGESIZE;
                    for (u = 0; u < PAGESIZE; u += size)
                    {
                        biti = bitbase + u / 16;
                        if (pool.freebits.test(biti))
                        {
                            List *list = cast(List *)(p + u);
                            if (list.next != bucket[bin])       // avoid unnecessary writes
                                list.next = bucket[bin];
                            bucket[bin] = list;
                        }
                    }
                }
            }
        }

        debug(COLLECT_PRINTF) printf("recovered pages = %d\n", recoveredpages);
        debug(COLLECT_PRINTF) printf("\tfree'd %u bytes, %u pages from %u pools\n", freed, freedpages, npools);

        return freedpages + recoveredpages;
    }


    /**
     *
     */
    uint getBits(Pool* pool, size_t biti)
    in
    {
        assert( pool );
    }
    body
    {
        uint bits;

        if (pool.finals.nbits &&
            pool.finals.test(biti))
            bits |= BlkAttr.FINALIZE;
        if (pool.noscan.test(biti))
            bits |= BlkAttr.NO_SCAN;
//        if (pool.nomove.nbits &&
//            pool.nomove.test(biti))
//            bits |= BlkAttr.NO_MOVE;
        return bits;
    }


    /**
     *
     */
    void setBits(Pool* pool, size_t biti, uint mask)
    in
    {
        assert( pool );
    }
    body
    {
        if (mask & BlkAttr.FINALIZE)
        {
            if (!pool.finals.nbits)
                pool.finals.alloc(pool.mark.nbits);
            pool.finals.set(biti);
        }
        if (mask & BlkAttr.NO_SCAN)
        {
            pool.noscan.set(biti);
        }
//        if (mask & BlkAttr.NO_MOVE)
//        {
//            if (!pool.nomove.nbits)
//                pool.nomove.alloc(pool.mark.nbits);
//            pool.nomove.set(biti);
//        }
    }


    /**
     *
     */
    void clrBits(Pool* pool, size_t biti, uint mask)
    in
    {
        assert( pool );
    }
    body
    {
        if (mask & BlkAttr.FINALIZE && pool.finals.nbits)
            pool.finals.clear(biti);
        if (mask & BlkAttr.NO_SCAN)
            pool.noscan.clear(biti);
//        if (mask & BlkAttr.NO_MOVE && pool.nomove.nbits)
//            pool.nomove.clear(biti);
    }

}


/* ============================ Pool  =============================== */


struct Pool
{
    byte* baseAddr;
    byte* topAddr;
    GCBits mark;     // entries already scanned, or should not be scanned
    GCBits scan;     // entries that need to be scanned
    GCBits freebits; // entries that are on the free list
    GCBits finals;   // entries that need finalizer run on them
    GCBits noscan;   // entries that should not be scanned

    size_t npages;
    ubyte* pagetable;


    void initialize(size_t npages)
    {
        size_t poolsize = npages * PAGESIZE;
        assert(poolsize >= POOLSIZE);
        baseAddr = cast(byte *) alloc.os_mem_map(poolsize);

        // Some of the code depends on page alignment of memory pools
        assert((cast(size_t)baseAddr & (PAGESIZE - 1)) == 0);

        if (!baseAddr)
        {
            npages = 0;
            poolsize = 0;
        }
        //assert(baseAddr);
        topAddr = baseAddr + poolsize;

        mark.alloc(cast(size_t)poolsize / 16);
        scan.alloc(cast(size_t)poolsize / 16);
        freebits.alloc(cast(size_t)poolsize / 16);
        noscan.alloc(cast(size_t)poolsize / 16);

        pagetable = cast(ubyte*) cstdlib.malloc(npages);
        if (!pagetable)
            onOutOfMemoryError();
        cstring.memset(pagetable, B_FREE, npages);

        this.npages = npages;
    }


    void Dtor()
    {
        if (baseAddr)
        {
            int result;

            if (npages)
            {
                result = alloc.os_mem_unmap(baseAddr, npages * PAGESIZE);
                assert(result);
                npages = 0;
            }

            baseAddr = null;
            topAddr = null;
        }
        // See Gcx.Dtor() for the rationale of the null check.
        if (pagetable)
            cstdlib.free(pagetable);

        mark.Dtor();
        scan.Dtor();
        freebits.Dtor();
        finals.Dtor();
        noscan.Dtor();
    }


    void Invariant() { }


    invariant
    {
        //mark.Invariant();
        //scan.Invariant();
        //freebits.Invariant();
        //finals.Invariant();
        //noscan.Invariant();

        if (baseAddr)
        {
            //if (baseAddr + npages * PAGESIZE != topAddr)
                //printf("baseAddr = %p, npages = %d, topAddr = %p\n", baseAddr, npages, topAddr);
            assert(baseAddr + npages * PAGESIZE == topAddr);
        }

        for (size_t i = 0; i < npages; i++)
        {
            Bins bin = cast(Bins)pagetable[i];
            assert(bin < B_MAX);
        }
    }


    /**
     * Allocate n pages from Pool.
     * Returns OPFAIL on failure.
     */
    size_t allocPages(size_t n)
    {
        size_t i;
        size_t n2;

        n2 = n;
        for (i = 0; i < npages; i++)
        {
            if (pagetable[i] == B_FREE)
            {
                if (--n2 == 0)
                    return i - n + 1;
            }
            else
                n2 = n;
        }
        return OPFAIL;
    }


    /**
     * Free npages pages starting with pagenum.
     */
    void freePages(size_t pagenum, size_t npages)
    {
        cstring.memset(&pagetable[pagenum], B_FREE, npages);
    }


    /**
     * Used for sorting pooltable[]
     */
    int opCmp(Pool *p2)
    {
        if (baseAddr < p2.baseAddr)
            return -1;
        else
        return cast(int)(baseAddr > p2.baseAddr);
    }
}


/* ============================ SENTINEL =============================== */


version (SENTINEL)
{
    const size_t SENTINEL_PRE = cast(size_t) 0xF4F4F4F4F4F4F4F4UL; // 32 or 64 bits
    const ubyte SENTINEL_POST = 0xF5;           // 8 bits
    const uint SENTINEL_EXTRA = 2 * size_t.sizeof + 1;


    size_t* sentinel_size(void *p)  { return &(cast(size_t *)p)[-2]; }
    size_t* sentinel_pre(void *p)   { return &(cast(size_t *)p)[-1]; }
    ubyte* sentinel_post(void *p) { return &(cast(ubyte *)p)[*sentinel_size(p)]; }


    void sentinel_init(void *p, size_t size)
    {
        *sentinel_size(p) = size;
        *sentinel_pre(p) = SENTINEL_PRE;
        *sentinel_post(p) = SENTINEL_POST;
    }


    void sentinel_Invariant(void *p)
    {
        assert(*sentinel_pre(p) == SENTINEL_PRE);
        assert(*sentinel_post(p) == SENTINEL_POST);
    }


    void *sentinel_add(void *p)
    {
        return p + 2 * size_t.sizeof;
    }


    void *sentinel_sub(void *p)
    {
        return p - 2 * size_t.sizeof;
    }
}
else
{
    const uint SENTINEL_EXTRA = 0;


    void sentinel_init(void *p, size_t size)
    {
    }


    void sentinel_Invariant(void *p)
    {
    }


    void *sentinel_add(void *p)
    {
        return p;
    }


    void *sentinel_sub(void *p)
    {
        return p;
    }
}


// vim: set et sw=4 sts=4 :
