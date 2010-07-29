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
//debug = PTRCHECK;             // more pointer checking
//debug = PTRCHECK2;            // thorough but slow pointer checking

/*************** Configuration *********************/

version = STACKGROWSDOWN;       // growing the stack means subtracting from the stack pointer
                                // (use for Intel X86 CPUs)
                                // else growing the stack means adding to the stack pointer

/***************************************************/

import rt.gc.cdgc.bits: GCBits;
import rt.gc.cdgc.stats: GCStats, Stats;
import dynarray = rt.gc.cdgc.dynarray;
import alloc = rt.gc.cdgc.alloc;
import opts = rt.gc.cdgc.opts;

import cstdlib = tango.stdc.stdlib;
import cstring = tango.stdc.string;

/*
 * This is a small optimization that proved it's usefulness. For small chunks
 * or memory memset() seems to be slower (probably because of the call) that
 * simply doing a simple loop to set the memory.
 */
void memset(void* dst, int c, size_t n)
{
    // This number (32) has been determined empirically
    if (n > 32) {
        cstring.memset(dst, c, n);
        return;
    }
    auto p = cast(ubyte*)(dst);
    while (n-- > 0)
        *p++ = c;
}

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

package enum BlkAttr : uint
{
    FINALIZE = 0b0000_0001,
    NO_SCAN  = 0b0000_0010,
    NO_MOVE  = 0b0000_0100,
    ALL_BITS = 0b1111_1111
}

package bool has_pointermap(uint attrs)
{
    return !opts.options.conservative && !(attrs & BlkAttr.NO_SCAN);
}

private
{

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
    int opCmp(in Range other)
    {
        if (pbot < other.pbot)
            return -1;
        else
        return cast(int)(pbot > other.pbot);
    }
}


const uint binsize[B_MAX] = [ 16,32,64,128,256,512,1024,2048,4096 ];
const uint notbinsize[B_MAX] = [ ~(16u-1),~(32u-1),~(64u-1),~(128u-1),~(256u-1),
                                ~(512u-1),~(1024u-1),~(2048u-1),~(4096u-1) ];


/* ============================ GC =============================== */


class GCLock { }                // just a dummy so we can get a global lock


struct GC
{
    ClassInfo lock;    // global lock

    void *p_cache;
    size_t size_cache;

    uint noStack;       // !=0 means don't scan stack
    uint anychanges;
    void *stackBottom;
    uint inited;
    int disabled;       // turn off collections if >0

    byte *minAddr;      // min(baseAddr)
    byte *maxAddr;      // max(topAddr)

    List *bucket[B_MAX];        // free list for each size

    dynarray.DynArray!(void*) roots;
    dynarray.DynArray!(Range) ranges;
    dynarray.DynArray!(Pool) pools;

    Stats stats;


    invariant
    {
        if (inited)
        {
        //printf("Gcx.invariant(): this = %p\n", this);
            size_t i;

            for (i = 0; i < pools.length; i++)
            {
                Pool* pool = pools[i];
                pool.Invariant();
                if (i == 0)
                {
                    assert(minAddr == pool.baseAddr);
                }
                if (i + 1 < pools.length)
                {
                    assert(*pool < pools[i + 1]);
                }
                else if (i + 1 == pools.length)
                {
                    assert(maxAddr == pool.topAddr);
                }
            }

            roots.Invariant();
            ranges.Invariant();

            for (i = 0; i < ranges.length; i++)
            {
                assert(ranges[i].pbot);
                assert(ranges[i].ptop);
                assert(ranges[i].pbot <= ranges[i].ptop);
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
     * Find Pool that pointer is in.
     * Return null if not in a Pool.
     * Assume pools is sorted.
     */
    Pool *findPool(void *p)
    {
        if (p >= minAddr && p < maxAddr)
        {
            if (pools.length == 1)
            {
                return pools[0];
            }

            for (size_t i = 0; i < pools.length; i++)
            {
                Pool* pool = pools[i];
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
            // getAttr
            ////////////////////////////////////////////////////////////////////

            info.attr = getAttr(pool, cast(size_t)(offset / 16));
            if (!(info.attr & BlkAttr.NO_SCAN))
                info.size -= (size_t*).sizeof;  // bitmask
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
     * Sort it into pools.
     * Mark all memory in the pool as B_FREE.
     * Return the actual number of bytes reserved or 0 on error.
     */
    size_t reserveNoSync(size_t size)
    {
        assert(size != 0);
        size_t npages = (size + PAGESIZE - 1) / PAGESIZE;
        Pool*  pool = newPool(npages);

        if (!pool)
            return 0;
        return pool.npages * PAGESIZE;
    }


    /**
     * Minimizes physical memory usage by returning free pools to the OS.
     */
    void minimizeNoSync()
    {
        size_t n;
        size_t pn;
        Pool*  pool;

        for (n = 0; n < pools.length; n++)
        {
            pool = pools[n];
            for (pn = 0; pn < pool.npages; pn++)
            {
                if (cast(Bins)pool.pagetable[pn] != B_FREE)
                    break;
            }
            if (pn < pool.npages)
                continue;
            pool.Dtor();
            pools.remove_at(n);
            n--;
        }
        minAddr = pools[0].baseAddr;
        maxAddr = pools[pools.length - 1].topAddr;
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

            for (n = 0; n < pools.length; n++)
            {
                pool = pools[n];
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
                if (freedpages >= pools.length * ((POOLSIZE / PAGESIZE) / 4))
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
            memset(&pool.pagetable[pn + 1], B_PAGEPLUS, npages - 1);
        p = pool.baseAddr + pn * PAGESIZE;
        memset(cast(char *)p + size, 0, npages * PAGESIZE - size);
        if (opts.options.mem_stomp)
            memset(p, 0xF1, size);
        return p;

      Lnomemory:
        return null; // let mallocNoSync handle the error
    }


    /**
     * Allocate a new pool with at least npages in it.
     * Sort it into pools.
     * Return null if failed.
     */
    Pool *newPool(size_t npages)
    {
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
        if (pools.length)
        {
            size_t n = pools.length;
            if (n > 8)
                n = 8;                  // cap pool size at 8 megs
            n *= (POOLSIZE / PAGESIZE);
            if (npages < n)
                npages = n;
        }

        Pool p;
        p.initialize(npages);
        if (!p.baseAddr)
        {
            p.Dtor();
            return null;
        }

        Pool* pool = pools.insert_sorted(p);
        if (pool)
        {
            minAddr = pools[0].baseAddr;
            maxAddr = pools[pools.length - 1].topAddr;
        }
        return pool;
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

        for (n = 0; n < pools.length; n++)
        {
            pool = pools[n];
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
     * Marks a range of memory using the conservative bit mask.  Used for
     * the stack, for the data segment, and additional memory ranges.
     */
    void mark_conservative(void* pbot, void* ptop)
    {
        mark(pbot, ptop, PointerMap.init.bits.ptr);
    }


    /**
     * Search a range of memory values and mark any pointers into the GC pool.
     */
    void mark(void *pbot, void *ptop, size_t* pm_bitmask)
    {
        const BITS_PER_WORD = size_t.sizeof * 8;

        void **p1 = cast(void **)pbot;
        void **p2 = cast(void **)ptop;
        size_t pcache = 0;
        uint changes = 0;

        size_t type_size = pm_bitmask[0];
        size_t* pm_bits = pm_bitmask + 1;

        //printf("marking range: %p -> %p\n", pbot, ptop);
        for (; p1 + type_size <= p2; p1 += type_size) {
            for (size_t n = 0; n < type_size; n++) {
                // scan bit set for this word
                if (!(pm_bits[n / BITS_PER_WORD] & (1 << (n % BITS_PER_WORD))))
                    continue;

                void* p = *(p1 + n);

                if (p < minAddr || p >= maxAddr)
                    continue;

                if ((cast(size_t)p & ~(PAGESIZE-1)) == pcache)
                    continue;

                Pool* pool = findPool(p);
                if (pool)
                {
                    size_t offset = cast(size_t)(p - pool.baseAddr);
                    size_t bit_i;
                    size_t pn = offset / PAGESIZE;
                    Bins   bin = cast(Bins)pool.pagetable[pn];

                    // Adjust bit to be at start of allocated memory block
                    if (bin <= B_PAGE)
                        bit_i = (offset & notbinsize[bin]) >> 4;
                    else if (bin == B_PAGEPLUS)
                    {
                        do
                        {
                            --pn;
                        }
                        while (cast(Bins)pool.pagetable[pn] == B_PAGEPLUS);
                        bit_i = pn * (PAGESIZE / 16);
                    }
                    else
                    {
                        // Don't mark bits in B_FREE pages
                        continue;
                    }

                    if (bin >= B_PAGE) // Cache B_PAGE and B_PAGEPLUS lookups
                        pcache = cast(size_t)p & ~(PAGESIZE-1);

                    if (!pool.mark.test(bit_i))
                    {
                        pool.mark.set(bit_i);
                        if (!pool.noscan.test(bit_i))
                        {
                            pool.scan.set(bit_i);
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
        stats.collection_started();
        scope (exit)
            stats.collection_finished();

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
        stats.world_stopped();

        p_cache = null;
        size_cache = 0;

        anychanges = 0;
        for (n = 0; n < pools.length; n++)
        {
            pool = pools[n];
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

        for (n = 0; n < pools.length; n++)
        {
            pool = pools[n];
            pool.mark.copy(&pool.freebits);
        }

        rt_scanStaticData( &mark_conservative );

        if (!noStack)
        {
            // Scan stacks and registers for each paused thread
            thread_scanAll( &mark_conservative, stackTop );
        }

        // Scan roots
        debug(COLLECT_PRINTF) printf("scan roots[]\n");
        mark_conservative(roots.ptr, roots.ptr + roots.length);

        // Scan ranges
        debug(COLLECT_PRINTF) printf("scan ranges[]\n");
        for (n = 0; n < ranges.length; n++)
        {
            debug(COLLECT_PRINTF) printf("\t%x .. %x\n", ranges[n].pbot, ranges[n].ptop);
            mark_conservative(ranges[n].pbot, ranges[n].ptop);
        }

        debug(COLLECT_PRINTF) printf("\tscan heap\n");
        while (anychanges)
        {
            anychanges = 0;
            for (n = 0; n < pools.length; n++)
            {
                uint *bbase;
                uint *b;
                uint *btop;

                pool = pools[n];

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
                        if (bin < B_PAGE) {
                            if (opts.options.conservative)
                                mark_conservative(o, o + binsize[bin]);
                            else {
                                auto end_of_blk = cast(size_t**)(o +
                                        binsize[bin] - size_t.sizeof);
                                size_t* pm_bitmask = *end_of_blk;
                                mark(o, end_of_blk, pm_bitmask);
                            }
                        }
                        else if (bin == B_PAGE || bin == B_PAGEPLUS)
                        {
                            if (bin == B_PAGEPLUS)
                            {
                                while (pool.pagetable[pn - 1] != B_PAGE)
                                    pn--;
                            }
                            u = 1;
                            while (pn + u < pool.npages &&
                                    pool.pagetable[pn + u] == B_PAGEPLUS)
                                u++;

                            size_t blk_size = u * PAGESIZE;
                            if (opts.options.conservative)
                                mark_conservative(o, o + blk_size);
                            else {
                                auto end_of_blk = cast(size_t**)(o + blk_size -
                                        size_t.sizeof);
                                size_t* pm_bitmask = *end_of_blk;
                                mark(o, end_of_blk, pm_bitmask);
                            }
                        }
                    }
                }
            }
        }

        thread_resumeAll();
        stats.world_started();

        // Free up everything not marked
        debug(COLLECT_PRINTF) printf("\tfree'ing\n");
        size_t freedpages = 0;
        size_t freed = 0;
        for (n = 0; n < pools.length; n++)
        {
            pool = pools[n];
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
                    size_t bit_i = pn * (PAGESIZE/16);
                    size_t bit_stride = size / 16;

    version(none) // BUG: doesn't work because freebits() must also be cleared
    {
                    // If free'd entire page
                    if (bbase[0] == 0 && bbase[1] == 0 && bbase[2] == 0 &&
                            bbase[3] == 0 && bbase[4] == 0 && bbase[5] == 0 &&
                            bbase[6] == 0 && bbase[7] == 0)
                    {
                        for (; p < ptop; p += size, bit_i += bit_stride)
                        {
                            if (pool.finals.nbits && pool.finals.testClear(bit_i)) {
                                if (opts.options.sentinel)
                                    rt_finalize(cast(List *)sentinel_add(p), false/*noStack > 0*/);
                                else
                                    rt_finalize(cast(List *)p, false/*noStack > 0*/);
                            }
                            this.clrAttr(pool, bit_i, BlkAttr.ALL_BITS);

                            List *list = cast(List *)p;

                            if (opts.options.mem_stomp)
                                memset(p, 0xF3, size);
                        }
                        pool.pagetable[pn] = B_FREE;
                        freed += PAGESIZE;
                        continue;
                    }
    }
                    for (; p < ptop; p += size, bit_i += bit_stride)
                    {
                        if (!pool.mark.test(bit_i))
                        {
                            if (opts.options.sentinel)
                                sentinel_Invariant(sentinel_add(p));

                            pool.freebits.set(bit_i);
                            if (pool.finals.nbits && pool.finals.testClear(bit_i)) {
                                if (opts.options.sentinel)
                                    rt_finalize(cast(List *)sentinel_add(p), false/*noStack > 0*/);
                                else
                                    rt_finalize(cast(List *)p, false/*noStack > 0*/);
                            }
                            clrAttr(pool, bit_i, BlkAttr.ALL_BITS);

                            List *list = cast(List *)p;

                            if (opts.options.mem_stomp)
                                memset(p, 0xF3, size);

                            freed += size;
                        }
                    }
                }
                else if (bin == B_PAGE)
                {
                    size_t bit_i = pn * (PAGESIZE / 16);
                    if (!pool.mark.test(bit_i))
                    {
                        byte *p = pool.baseAddr + pn * PAGESIZE;
                        if (opts.options.sentinel)
                            sentinel_Invariant(sentinel_add(p));
                        if (pool.finals.nbits && pool.finals.testClear(bit_i)) {
                            if (opts.options.sentinel)
                                rt_finalize(sentinel_add(p), false/*noStack > 0*/);
                            else
                                rt_finalize(p, false/*noStack > 0*/);
                        }
                        clrAttr(pool, bit_i, BlkAttr.ALL_BITS);

                        debug(COLLECT_PRINTF) printf("\tcollecting big %x\n", p);
                        pool.pagetable[pn] = B_FREE;
                        freedpages++;
                        if (opts.options.mem_stomp)
                            memset(p, 0xF3, PAGESIZE);
                        while (pn + 1 < pool.npages && pool.pagetable[pn + 1] == B_PAGEPLUS)
                        {
                            pn++;
                            pool.pagetable[pn] = B_FREE;
                            freedpages++;

                            if (opts.options.mem_stomp)
                            {
                                p += PAGESIZE;
                                memset(p, 0xF3, PAGESIZE);
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
        for (n = 0; n < pools.length; n++)
        {
            pool = pools[n];
            for (size_t pn = 0; pn < pool.npages; pn++)
            {
                Bins   bin = cast(Bins)pool.pagetable[pn];
                size_t bit_i;
                size_t u;

                if (bin < B_PAGE)
                {
                    size_t size = binsize[bin];
                    size_t bit_stride = size / 16;
                    size_t bit_base = pn * (PAGESIZE / 16);
                    size_t bit_top = bit_base + (PAGESIZE / 16);
                    byte*  p;

                    bit_i = bit_base;
                    for (; bit_i < bit_top; bit_i += bit_stride)
                    {
                        if (!pool.freebits.test(bit_i))
                            goto Lnotfree;
                    }
                    pool.pagetable[pn] = B_FREE;
                    recoveredpages++;
                    continue;

                 Lnotfree:
                    p = pool.baseAddr + pn * PAGESIZE;
                    for (u = 0; u < PAGESIZE; u += size)
                    {
                        bit_i = bit_base + u / 16;
                        if (pool.freebits.test(bit_i))
                        {
                            List *list = cast(List *)(p + u);
                            // avoid unnecessary writes
                            if (list.next != bucket[bin])
                                list.next = bucket[bin];
                            bucket[bin] = list;
                        }
                    }
                }
            }
        }

        debug(COLLECT_PRINTF) printf("recovered pages = %d\n", recoveredpages);
        debug(COLLECT_PRINTF) printf("\tfree'd %u bytes, %u pages from %u pools\n", freed, freedpages, pools.length);

        return freedpages + recoveredpages;
    }


    /**
     *
     */
    uint getAttr(Pool* pool, size_t bit_i)
    in
    {
        assert( pool );
    }
    body
    {
        uint attrs;

        if (pool.finals.nbits &&
            pool.finals.test(bit_i))
            attrs |= BlkAttr.FINALIZE;
        if (pool.noscan.test(bit_i))
            attrs |= BlkAttr.NO_SCAN;
//        if (pool.nomove.nbits &&
//            pool.nomove.test(bit_i))
//            attrs |= BlkAttr.NO_MOVE;
        return attrs;
    }


    /**
     *
     */
    void setAttr(Pool* pool, size_t bit_i, uint mask)
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
            pool.finals.set(bit_i);
        }
        if (mask & BlkAttr.NO_SCAN)
        {
            pool.noscan.set(bit_i);
        }
//        if (mask & BlkAttr.NO_MOVE)
//        {
//            if (!pool.nomove.nbits)
//                pool.nomove.alloc(pool.mark.nbits);
//            pool.nomove.set(bit_i);
//        }
    }


    /**
     *
     */
    void clrAttr(Pool* pool, size_t bit_i, uint mask)
    in
    {
        assert( pool );
    }
    body
    {
        if (mask & BlkAttr.FINALIZE && pool.finals.nbits)
            pool.finals.clear(bit_i);
        if (mask & BlkAttr.NO_SCAN)
            pool.noscan.clear(bit_i);
//        if (mask & BlkAttr.NO_MOVE && pool.nomove.nbits)
//            pool.nomove.clear(bit_i);
    }



    void initialize()
    {
        int dummy;
        stackBottom = cast(char*)&dummy;
        opts.parse(cstdlib.getenv("D_GC_OPTS"));
        lock = GCLock.classinfo;
        inited = 1;
        setStackBottom(rt_stackBottom());
        stats = Stats(this);
    }


    /**
     *
     */
    void enable()
    {
        if (!thread_needLock())
        {
            assert(this.disabled > 0);
            this.disabled--;
        }
        else synchronized (lock)
        {
            assert(this.disabled > 0);
            this.disabled--;
        }
    }


    /**
     *
     */
    void disable()
    {
        if (!thread_needLock())
        {
            this.disabled++;
        }
        else synchronized (lock)
        {
            this.disabled++;
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
            Pool* pool = this.findPool(p);
            uint  old_attrs = 0;

            if (pool)
            {
                auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;

                old_attrs = this.getAttr(pool, bit_i);
            }
            return old_attrs;
        }

        if (!thread_needLock())
        {
            return go();
        }
        else synchronized (lock)
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
            Pool* pool = this.findPool(p);
            uint  old_attrs = 0;

            if (pool)
            {
                auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;

                old_attrs = this.getAttr(pool, bit_i);
                this.setAttr(pool, bit_i, mask);
            }
            return old_attrs;
        }

        if (!thread_needLock())
        {
            return go();
        }
        else synchronized (lock)
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
            Pool* pool = this.findPool(p);
            uint  old_attrs = 0;

            if (pool)
            {
                auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;

                old_attrs = this.getAttr(pool, bit_i);
                this.clrAttr(pool, bit_i, mask);
            }
            return old_attrs;
        }

        if (!thread_needLock())
        {
            return go();
        }
        else synchronized (lock)
        {
            return go();
        }
    }


    /**
     *
     */
    void *malloc(size_t size, uint attrs, PointerMap ptrmap)
    {
        if (!size)
        {
            return null;
        }

        if (!thread_needLock())
        {
            return mallocNoSync(size, attrs, ptrmap.bits.ptr);
        }
        else synchronized (lock)
        {
            return mallocNoSync(size, attrs, ptrmap.bits.ptr);
        }
    }


    //
    //
    //
    private void *mallocNoSync(size_t size, uint attrs, size_t* pm_bitmask)
    {
        assert(size != 0);

        stats.malloc_started(size, attrs, pm_bitmask);
        scope (exit)
            stats.malloc_finished(p);

        void *p = null;
        Bins bin;

        if (opts.options.sentinel)
            size += SENTINEL_EXTRA;

        bool has_pm = has_pointermap(attrs);
        if (has_pm)
            size += size_t.sizeof;

        // Compute size bin
        // Cache previous binsize lookup - Dave Fladebo.
        static size_t lastsize = -1;
        static Bins lastbin;
        if (size == lastsize)
            bin = lastbin;
        else
        {
            bin = this.findBin(size);
            lastsize = size;
            lastbin = bin;
        }

        size_t capacity; // to figure out where to store the bitmask
        if (bin < B_PAGE)
        {
            p = this.bucket[bin];
            if (p is null)
            {
                if (!this.allocPage(bin) && !this.disabled)   // try to find a new page
                {
                    if (!thread_needLock())
                    {
                        /* Then we haven't locked it yet. Be sure
                         * and lock for a collection, since a finalizer
                         * may start a new thread.
                         */
                        synchronized (lock)
                        {
                            this.fullcollectshell();
                        }
                    }
                    else if (!this.fullcollectshell())       // collect to find a new page
                    {
                        //this.newPool(1);
                    }
                }
                if (!this.bucket[bin] && !this.allocPage(bin))
                {
                    this.newPool(1);         // allocate new pool to find a new page
                    int result = this.allocPage(bin);
                    if (!result)
                        onOutOfMemoryError();
                }
                p = this.bucket[bin];
            }
            capacity = binsize[bin];

            // Return next item from free list
            this.bucket[bin] = (cast(List*)p).next;
            if (!(attrs & BlkAttr.NO_SCAN))
                memset(p + size, 0, capacity - size);
            if (opts.options.mem_stomp)
                memset(p, 0xF0, size);
        }
        else
        {
            p = this.bigAlloc(size);
            if (!p)
                onOutOfMemoryError();
            // Round the size up to the number of pages needed to store it
            size_t npages = (size + PAGESIZE - 1) / PAGESIZE;
            capacity = npages * PAGESIZE;
        }

        // Store the bit mask AFTER SENTINEL_POST
        // TODO: store it BEFORE, so the bitmask is protected too
        if (has_pm) {
            auto end_of_blk = cast(size_t**)(p + capacity - size_t.sizeof);
            *end_of_blk = pm_bitmask;
            size -= size_t.sizeof;
        }

        if (opts.options.sentinel) {
            size -= SENTINEL_EXTRA;
            p = sentinel_add(p);
            sentinel_init(p, size);
        }

        if (attrs)
        {
            Pool *pool = this.findPool(p);
            assert(pool);

            this.setAttr(pool, cast(size_t)(p - pool.baseAddr) / 16, attrs);
        }
        return p;
    }


    /**
     *
     */
    void *calloc(size_t size, uint attrs, PointerMap ptrmap)
    {
        if (!size)
        {
            return null;
        }

        if (!thread_needLock())
        {
            return callocNoSync(size, attrs, ptrmap.bits.ptr);
        }
        else synchronized (lock)
        {
            return callocNoSync(size, attrs, ptrmap.bits.ptr);
        }
    }


    //
    //
    //
    private void *callocNoSync(size_t size, uint attrs, size_t* pm_bitmask)
    {
        assert(size != 0);

        void *p = mallocNoSync(size, attrs, pm_bitmask);
        memset(p, 0, size);
        return p;
    }


    /**
     *
     */
    void *realloc(void *p, size_t size, uint attrs, PointerMap ptrmap)
    {
        if (!thread_needLock())
        {
            return reallocNoSync(p, size, attrs, ptrmap.bits.ptr);
        }
        else synchronized (lock)
        {
            return reallocNoSync(p, size, attrs, ptrmap.bits.ptr);
        }
    }


    //
    //
    //
    private void *reallocNoSync(void *p, size_t size, uint attrs,
            size_t* pm_bitmask)
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
            p = mallocNoSync(size, attrs, pm_bitmask);
        }
        else
        {
            Pool* pool = this.findPool(p);
            if (pool is null)
                return null;

            // Set or retrieve attributes as appropriate
            auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;
            if (attrs) {
                this.clrAttr(pool, bit_i, BlkAttr.ALL_BITS);
                this.setAttr(pool, bit_i, attrs);
            }
            else
                attrs = this.getAttr(pool, bit_i);

            void* blk_base_addr = this.findBase(p);
            size_t blk_size = this.findSize(p);
            bool has_pm = has_pointermap(attrs);
            size_t pm_bitmask_size = 0;
            if (has_pm) {
                pm_bitmask_size = size_t.sizeof;
                // Retrieve pointer map bit mask if appropriate
                if (pm_bitmask is null) {
                    auto end_of_blk = cast(size_t**)(blk_base_addr +
                            blk_size - size_t.sizeof);
                    pm_bitmask = *end_of_blk;
                }
            }

            if (opts.options.sentinel)
            {
                sentinel_Invariant(p);
                size_t sentinel_stored_size = *sentinel_size(p);
                if (sentinel_stored_size != size)
                {
                    void* p2 = mallocNoSync(size, attrs, pm_bitmask);
                    if (sentinel_stored_size < size)
                        size = sentinel_stored_size;
                    cstring.memcpy(p2, p, size);
                    p = p2;
                }
            }
            else
            {
                size += pm_bitmask_size;
                if (blk_size >= PAGESIZE && size >= PAGESIZE)
                {
                    auto psz = blk_size / PAGESIZE;
                    auto newsz = (size + PAGESIZE - 1) / PAGESIZE;
                    if (newsz == psz)
                        return p;

                    auto pagenum = (p - pool.baseAddr) / PAGESIZE;

                    if (newsz < psz)
                    {
                        // Shrink in place
                        synchronized (lock)
                        {
                            if (opts.options.mem_stomp)
                                memset(p + size - pm_bitmask_size, 0xF2,
                                        blk_size - size - pm_bitmask_size);
                            pool.freePages(pagenum + newsz, psz - newsz);
                        }
                        if (has_pm) {
                            auto end_of_blk = cast(size_t**)(
                                    blk_base_addr + (PAGESIZE * newsz) -
                                    pm_bitmask_size);
                            *end_of_blk = pm_bitmask;
                        }
                        return p;
                    }
                    else if (pagenum + newsz <= pool.npages)
                    {
                        // Attempt to expand in place
                        synchronized (lock)
                        {
                            for (size_t i = pagenum + psz; 1;)
                            {
                                if (i == pagenum + newsz)
                                {
                                    if (opts.options.mem_stomp)
                                        memset(p + blk_size - pm_bitmask_size,
                                                0xF0, size - blk_size
                                                - pm_bitmask_size);
                                    memset(pool.pagetable + pagenum +
                                            psz, B_PAGEPLUS, newsz - psz);
                                    if (has_pm) {
                                        auto end_of_blk = cast(size_t**)(
                                                blk_base_addr +
                                                (PAGESIZE * newsz) -
                                                pm_bitmask_size);
                                        *end_of_blk = pm_bitmask;
                                    }
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
                // if new size is bigger or less than half
                if (blk_size < size || blk_size > size * 2)
                {
                    size -= pm_bitmask_size;
                    blk_size -= pm_bitmask_size;
                    void* p2 = mallocNoSync(size, attrs, pm_bitmask);
                    if (blk_size < size)
                        size = blk_size;
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
        else synchronized (lock)
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
        if (opts.options.sentinel)
            return 0;

        Pool* pool = this.findPool(p);
        if (pool is null)
            return 0;

        // Retrieve attributes
        auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;
        uint attrs = this.getAttr(pool, bit_i);

        void* blk_base_addr = this.findBase(p);
        size_t blk_size = this.findSize(p);
        bool has_pm = has_pointermap(attrs);
        size_t* pm_bitmask = null;
        size_t pm_bitmask_size = 0;
        if (has_pm) {
            pm_bitmask_size = size_t.sizeof;
            // Retrieve pointer map bit mask
            auto end_of_blk = cast(size_t**)(blk_base_addr +
                    blk_size - size_t.sizeof);
            pm_bitmask = *end_of_blk;

            minsize += size_t.sizeof;
            maxsize += size_t.sizeof;
        }

        if (blk_size < PAGESIZE)
            return 0; // cannot extend buckets

        auto psz = blk_size / PAGESIZE;
        auto minsz = (minsize + PAGESIZE - 1) / PAGESIZE;
        auto maxsz = (maxsize + PAGESIZE - 1) / PAGESIZE;

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

        size_t new_size = (psz + sz) * PAGESIZE;

        if (opts.options.mem_stomp)
            memset(p + blk_size - pm_bitmask_size, 0xF0,
                    new_size - blk_size - pm_bitmask_size);
        memset(pool.pagetable + pagenum + psz, B_PAGEPLUS, sz);
        this.p_cache = null;
        this.size_cache = 0;

        if (has_pm) {
            new_size -= size_t.sizeof;
            auto end_of_blk = cast(size_t**)(blk_base_addr + new_size);
            *end_of_blk = pm_bitmask;
        }
        return new_size;
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
        else synchronized (lock)
        {
            return reserveNoSync(size);
        }
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
        else synchronized (lock)
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
        size_t bit_i;

        // Find which page it is in
        pool = this.findPool(p);
        if (!pool)                              // if not one of ours
            return;                             // ignore
        if (opts.options.sentinel) {
            sentinel_Invariant(p);
            p = sentinel_sub(p);
        }
        pagenum = cast(size_t)(p - pool.baseAddr) / PAGESIZE;
        bit_i = cast(size_t)(p - pool.baseAddr) / 16;
        this.clrAttr(pool, bit_i, BlkAttr.ALL_BITS);

        bin = cast(Bins)pool.pagetable[pagenum];
        if (bin == B_PAGE)              // if large alloc
        {
            // Free pages
            size_t npages = 1;
            size_t n = pagenum;
            while (++n < pool.npages && pool.pagetable[n] == B_PAGEPLUS)
                npages++;
            if (opts.options.mem_stomp)
                memset(p, 0xF2, npages * PAGESIZE);
            pool.freePages(pagenum, npages);
        }
        else
        {
            // Add to free list
            List *list = cast(List*)p;

            if (opts.options.mem_stomp)
                memset(p, 0xF2, binsize[bin]);

            list.next = this.bucket[bin];
            this.bucket[bin] = list;
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
        else synchronized (lock)
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

        return this.findBase(p);
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
        else synchronized (lock)
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

        if (opts.options.sentinel)
            p = sentinel_sub(p);

        Pool* pool = this.findPool(p);
        if (pool is null)
            return 0;

        auto biti = cast(size_t)(p - pool.baseAddr) / 16;
        uint attrs = this.getAttr(pool, biti);

        size_t size = this.findSize(p);
        size_t pm_bitmask_size = 0;
        if (has_pointermap(attrs))
            pm_bitmask_size = size_t.sizeof;

        if (opts.options.sentinel) {
            // Check for interior pointer
            // This depends on:
            // 1) size is a power of 2 for less than PAGESIZE values
            // 2) base of memory pool is aligned on PAGESIZE boundary
            if (cast(size_t)p & (size - 1) & (PAGESIZE - 1))
                return 0;
            return size - SENTINEL_EXTRA - pm_bitmask_size;
        }
        else {
            if (p == this.p_cache)
                return this.size_cache;

            // Check for interior pointer
            // This depends on:
            // 1) size is a power of 2 for less than PAGESIZE values
            // 2) base of memory pool is aligned on PAGESIZE boundary
            if (cast(size_t)p & (size - 1) & (PAGESIZE - 1))
                return 0;

            this.p_cache = p;
            this.size_cache = size - pm_bitmask_size;

            return this.size_cache;
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
        else synchronized (lock)
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

        return this.getInfo(p);
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
        else synchronized (lock)
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

        if (opts.options.sentinel)
            sentinel_Invariant(p);
        debug (PTRCHECK)
        {
            Pool*  pool;
            size_t pagenum;
            Bins   bin;
            size_t size;

            if (opts.options.sentinel)
                p = sentinel_sub(p);
            pool = this.findPool(p);
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

                    for (list = this.bucket[bin]; list; list = list.next)
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
            if (p > this.stackBottom)
            {
                this.stackBottom = p;
            }
        }
        else
        {
            //p = (void *)((uint *)p - 4);
            if (p < this.stackBottom)
            {
                this.stackBottom = cast(char*)p;
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
            if (roots.append(p) is null)
                onOutOfMemoryError();
        }
        else synchronized (lock)
        {
            if (roots.append(p) is null)
                onOutOfMemoryError();
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

        bool r;
        if (!thread_needLock())
        {
            r = roots.remove(p);
        }
        else synchronized (lock)
        {
            r = roots.remove(p);
        }
        assert (r);
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
            if (ranges.append(Range(p, p+sz)) is null)
                onOutOfMemoryError();
        }
        else synchronized (lock)
        {
            if (ranges.append(Range(p, p+sz)) is null)
                onOutOfMemoryError();
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

        bool r;
        if (!thread_needLock())
        {
            r = ranges.remove(Range(p, null));
        }
        else synchronized (lock)
        {
            r = ranges.remove(Range(p, null));
        }
        assert (r);
    }


    /**
     * do full garbage collection
     */
    void fullCollect()
    {

        if (!thread_needLock())
        {
            this.fullcollectshell();
        }
        else synchronized (lock)
        {
            this.fullcollectshell();
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
            this.noStack++;
            this.fullcollectshell();
            this.noStack--;
        }
        else synchronized (lock)
        {
            this.noStack++;
            this.fullcollectshell();
            this.noStack--;
        }
    }


    /**
     * minimize free space usage
     */
    void minimize()
    {
        if (!thread_needLock())
        {
            this.minimizeNoSync();
        }
        else synchronized (lock)
        {
            this.minimizeNoSync();
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
        else synchronized (lock)
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

        memset(&stats, 0, GCStats.sizeof);

        for (n = 0; n < pools.length; n++)
        {
            Pool* pool = pools[n];
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
            for (List *list = this.bucket[n]; list; list = list.next)
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
            synchronized(lock) return code();
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
        memset(pagetable, B_FREE, npages);

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
        memset(&pagetable[pagenum], B_FREE, npages);
    }


    /**
     * Used for sorting pools
     */
    int opCmp(in Pool other)
    {
        if (baseAddr < other.baseAddr)
            return -1;
        else
        return cast(int)(baseAddr > other.baseAddr);
    }
}


/* ============================ SENTINEL =============================== */


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


// vim: set et sw=4 sts=4 :
