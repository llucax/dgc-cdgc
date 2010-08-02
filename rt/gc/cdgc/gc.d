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
    alias void delegate(Object) DEvent;
    alias void delegate( void*, void* ) scanFn;
    enum { OPFAIL = ~cast(size_t)0 }

    extern (C)
    {
        version (DigitalMars) version(OSX)
            oid _d_osx_image_init();

        void* rt_stackBottom();
        void* rt_stackTop();
        void rt_finalize( void* p, bool det = true );
        void rt_attachDisposeEvent(Object h, DEvent e);
        bool rt_detachDisposeEvent(Object h, DEvent e);
        void rt_scanStaticData( scanFn scan );

        void thread_init();
        bool thread_needLock();
        void thread_suspendAll();
        void thread_resumeAll();
        void thread_scanAll( scanFn fn, void* curStackTop = null );

        void onOutOfMemoryError();
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


class GCLock {} // just a dummy so we can get a global lock


struct GC
{
    // global lock
    ClassInfo lock;

    void* p_cache;
    size_t size_cache;

    // !=0 means don't scan stack
    uint no_stack;
    bool any_changes;
    void* stack_bottom;
    uint inited;
    /// Turn off collections if > 0
    int disabled;

    /// min(pool.baseAddr)
    byte *min_addr;
    /// max(pool.topAddr)
    byte *max_addr;

    /// Free list for each size
    List*[B_MAX] free_list;

    dynarray.DynArray!(void*) roots;
    dynarray.DynArray!(Range) ranges;
    dynarray.DynArray!(Pool) pools;

    Stats stats;
}

// call locked if necessary
private T locked(T, alias Code)()
{
    if (thread_needLock())
        synchronized (gc.lock) return Code();
    else
       return Code();
}

private GC* gc;

bool Invariant()
{
    assert (gc !is null);
    if (gc.inited) {
        for (size_t i = 0; i < gc.pools.length; i++) {
            Pool* pool = gc.pools[i];
            pool.Invariant();
            if (i == 0)
                assert(gc.min_addr == pool.baseAddr);
            if (i + 1 < gc.pools.length)
                assert(*pool < gc.pools[i + 1]);
            else if (i + 1 == gc.pools.length)
                assert(gc.max_addr == pool.topAddr);
        }

        gc.roots.Invariant();
        gc.ranges.Invariant();

        for (size_t i = 0; i < gc.ranges.length; i++) {
            assert(gc.ranges[i].pbot);
            assert(gc.ranges[i].ptop);
            assert(gc.ranges[i].pbot <= gc.ranges[i].ptop);
        }

        for (size_t i = 0; i < B_PAGE; i++)
            for (List *list = gc.free_list[i]; list; list = list.next)
            {
            }
    }
    return true;
}


/**
 * Find Pool that pointer is in.
 * Return null if not in a Pool.
 * Assume pools is sorted.
 */
Pool *findPool(void *p)
{
    if (p >= gc.min_addr && p < gc.max_addr)
    {
        if (gc.pools.length == 1)
        {
            return gc.pools[0];
        }

        for (size_t i = 0; i < gc.pools.length; i++)
        {
            Pool* pool = gc.pools[i];
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
 * Determine the base address of the block containing p.  If p is not a gc
 * allocated pointer, return null.
 */
BlkInfo getInfo(void* p)
{
    assert (p !is null);
    Pool* pool = findPool(p);
    if (pool is null)
        return BlkInfo.init;
    BlkInfo info;
    info.base = pool.findBase(p);
    info.size = pool.findSize(info.base);
    info.attr = getAttr(pool, cast(size_t)(info.base - pool.baseAddr) / 16u);
    if (has_pointermap(info.attr)) {
        info.size -= size_t.sizeof; // PointerMap bitmask
        // Points to the PointerMap bitmask pointer, not user data
        if (p >= (info.base + info.size)) {
            return BlkInfo.init;
        }
    }
    if (opts.options.sentinel) {
        info.base = sentinel_add(info.base);
        // points to sentinel data, not user data
        if (p < info.base || p >= sentinel_post(info.base))
            return BlkInfo.init;
        info.size -= SENTINEL_EXTRA;
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
size_t reserve(size_t size)
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
void minimize()
{
    size_t n;
    size_t pn;
    Pool*  pool;

    for (n = 0; n < gc.pools.length; n++)
    {
        pool = gc.pools[n];
        for (pn = 0; pn < pool.npages; pn++)
        {
            if (cast(Bins)pool.pagetable[pn] != B_FREE)
                break;
        }
        if (pn < pool.npages)
            continue;
        pool.Dtor();
        gc.pools.remove_at(n);
        n--;
    }
    gc.min_addr = gc.pools[0].baseAddr;
    gc.max_addr = gc.pools[gc.pools.length - 1].topAddr;
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

        for (n = 0; n < gc.pools.length; n++)
        {
            pool = gc.pools[n];
            pn = pool.allocPages(npages);
            if (pn != OPFAIL)
                goto L1;
        }

        // Failed
        switch (state)
        {
        case 0:
            if (gc.disabled)
            {
                state = 1;
                continue;
            }
            // Try collecting
            freedpages = fullcollectshell();
            if (freedpages >= gc.pools.length * ((POOLSIZE / PAGESIZE) / 4))
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
    if (gc.pools.length)
    {
        size_t n = gc.pools.length;
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

    Pool* pool = gc.pools.insert_sorted(p);
    if (pool)
    {
        gc.min_addr = gc.pools[0].baseAddr;
        gc.max_addr = gc.pools[gc.pools.length - 1].topAddr;
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

    for (n = 0; n < gc.pools.length; n++)
    {
        pool = gc.pools[n];
        pn = pool.allocPages(1);
        if (pn != OPFAIL)
            goto L1;
    }
    return 0;               // failed

  L1:
    pool.pagetable[pn] = cast(ubyte)bin;

    // Convert page to free list
    size_t size = binsize[bin];
    List **b = &gc.free_list[bin];

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
    // TODO: make our own assert because assert uses the GC
    assert (pbot <= ptop);

    const BITS_PER_WORD = size_t.sizeof * 8;

    void **p1 = cast(void **)pbot;
    void **p2 = cast(void **)ptop;
    size_t pcache = 0;
    uint changes = 0;

    size_t type_size = pm_bitmask[0];
    size_t* pm_bits = pm_bitmask + 1;
    bool has_type_info = type_size != 1 || pm_bits[0] != 1 || pm_bits[1] != 0;

    //printf("marking range: %p -> %p\n", pbot, ptop);
    for (; p1 + type_size <= p2; p1 += type_size) {
        size_t n = 0;
        if (has_type_info) {
            while (n < type_size && pm_bits[n / BITS_PER_WORD] == 0)
                n += BITS_PER_WORD;
            if (n < type_size && (pm_bits[n / BITS_PER_WORD] &
                        ((1 << (BITS_PER_WORD / 2)) - 1)) == 0)
                n += BITS_PER_WORD / 2;
            else if (n < type_size && (pm_bits[n / BITS_PER_WORD] &
                        ((1 << (BITS_PER_WORD / 4)) - 1)) == 0)
                n += BITS_PER_WORD / 4;
        }
        for (; n < type_size; n++) {
            // scan bit set for this word
            if (has_type_info &&
                    !(pm_bits[n / BITS_PER_WORD] & (1 << (n % BITS_PER_WORD))))
                continue;

            void* p = *(p1 + n);

            if (p < gc.min_addr || p >= gc.max_addr)
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
    if (changes)
        gc.any_changes = true;
}

/**
 * Return number of full pages free'd.
 */
size_t fullcollectshell()
{
    gc.stats.collection_started();
    scope (exit)
        gc.stats.collection_finished();

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
    gc.stats.world_stopped();

    gc.p_cache = null;
    gc.size_cache = 0;

    gc.any_changes = false;
    for (n = 0; n < gc.pools.length; n++)
    {
        pool = gc.pools[n];
        pool.mark.zero();
        pool.scan.zero();
        pool.freebits.zero();
    }

    // Mark each free entry, so it doesn't get scanned
    for (n = 0; n < B_PAGE; n++)
    {
        for (List *list = gc.free_list[n]; list; list = list.next)
        {
            pool = findPool(list);
            assert(pool);
            pool.freebits.set(cast(size_t)(cast(byte*)list - pool.baseAddr) / 16);
        }
    }

    for (n = 0; n < gc.pools.length; n++)
    {
        pool = gc.pools[n];
        pool.mark.copy(&pool.freebits);
    }

    void mark_conservative_dg(void* pbot, void* ptop)
    {
        mark_conservative(pbot, ptop);
    }

    rt_scanStaticData(&mark_conservative_dg);

    if (!gc.no_stack)
    {
        // Scan stacks and registers for each paused thread
        thread_scanAll(&mark_conservative_dg, stackTop);
    }

    // Scan roots
    debug(COLLECT_PRINTF) printf("scan roots[]\n");
    mark_conservative(gc.roots.ptr, gc.roots.ptr + gc.roots.length);

    // Scan ranges
    debug(COLLECT_PRINTF) printf("scan ranges[]\n");
    for (n = 0; n < gc.ranges.length; n++)
    {
        debug(COLLECT_PRINTF) printf("\t%x .. %x\n", gc.ranges[n].pbot, gc.ranges[n].ptop);
        mark_conservative(gc.ranges[n].pbot, gc.ranges[n].ptop);
    }

    debug(COLLECT_PRINTF) printf("\tscan heap\n");
    while (gc.any_changes)
    {
        gc.any_changes = false;
        for (n = 0; n < gc.pools.length; n++)
        {
            uint *bbase;
            uint *b;
            uint *btop;

            pool = gc.pools[n];

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
    gc.stats.world_started();

    // Free up everything not marked
    debug(COLLECT_PRINTF) printf("\tfree'ing\n");
    size_t freedpages = 0;
    size_t freed = 0;
    for (n = 0; n < gc.pools.length; n++)
    {
        pool = gc.pools[n];
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
                                rt_finalize(cast(List *)sentinel_add(p), false/*gc.no_stack > 0*/);
                            else
                                rt_finalize(cast(List *)p, false/*gc.no_stack > 0*/);
                        }
                        clrAttr(pool, bit_i, BlkAttr.ALL_BITS);

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
                                rt_finalize(cast(List *)sentinel_add(p), false/*gc.no_stack > 0*/);
                            else
                                rt_finalize(cast(List *)p, false/*gc.no_stack > 0*/);
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
                            rt_finalize(sentinel_add(p), false/*gc.no_stack > 0*/);
                        else
                            rt_finalize(p, false/*gc.no_stack > 0*/);
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
    gc.free_list[] = null;

    // Free complete pages, rebuild free list
    debug(COLLECT_PRINTF) printf("\tfree complete pages\n");
    size_t recoveredpages = 0;
    for (n = 0; n < gc.pools.length; n++)
    {
        pool = gc.pools[n];
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
                        if (list.next != gc.free_list[bin])
                            list.next = gc.free_list[bin];
                        gc.free_list[bin] = list;
                    }
                }
            }
        }
    }

    debug(COLLECT_PRINTF) printf("recovered pages = %d\n", recoveredpages);
    debug(COLLECT_PRINTF) printf("\tfree'd %u bytes, %u pages from %u pools\n", freed, freedpages, gc.pools.length);

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
    gc.stack_bottom = cast(char*)&dummy;
    opts.parse(cstdlib.getenv("D_GC_OPTS"));
    gc.lock = GCLock.classinfo;
    gc.inited = 1;
    setStackBottom(rt_stackBottom());
    gc.stats = Stats(gc);
}


//
//
//
private void *malloc(size_t size, uint attrs, size_t* pm_bitmask)
{
    assert(size != 0);

    gc.stats.malloc_started(size, attrs, pm_bitmask);
    scope (exit)
        gc.stats.malloc_finished(p);

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
        bin = findBin(size);
        lastsize = size;
        lastbin = bin;
    }

    size_t capacity; // to figure out where to store the bitmask
    if (bin < B_PAGE)
    {
        p = gc.free_list[bin];
        if (p is null)
        {
            if (!allocPage(bin) && !gc.disabled)   // try to find a new page
            {
                if (!thread_needLock())
                {
                    /* Then we haven't locked it yet. Be sure
                     * and gc.lock for a collection, since a finalizer
                     * may start a new thread.
                     */
                    synchronized (gc.lock)
                    {
                        fullcollectshell();
                    }
                }
                else if (!fullcollectshell())       // collect to find a new page
                {
                    //newPool(1);
                }
            }
            if (!gc.free_list[bin] && !allocPage(bin))
            {
                newPool(1);         // allocate new pool to find a new page
                int result = allocPage(bin);
                if (!result)
                    onOutOfMemoryError();
            }
            p = gc.free_list[bin];
        }
        capacity = binsize[bin];

        // Return next item from free list
        gc.free_list[bin] = (cast(List*)p).next;
        if (!(attrs & BlkAttr.NO_SCAN))
            memset(p + size, 0, capacity - size);
        if (opts.options.mem_stomp)
            memset(p, 0xF0, size);
    }
    else
    {
        p = bigAlloc(size);
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
        Pool *pool = findPool(p);
        assert(pool);

        setAttr(pool, cast(size_t)(p - pool.baseAddr) / 16, attrs);
    }
    return p;
}


//
//
//
private void *calloc(size_t size, uint attrs, size_t* pm_bitmask)
{
    assert(size != 0);

    void *p = malloc(size, attrs, pm_bitmask);
    memset(p, 0, size);
    return p;
}


//
//
//
private void *realloc(void *p, size_t size, uint attrs,
        size_t* pm_bitmask)
{
    if (!size)
    {
        if (p)
        {
            free(p);
            p = null;
        }
    }
    else if (!p)
    {
        p = malloc(size, attrs, pm_bitmask);
    }
    else
    {
        Pool* pool = findPool(p);
        if (pool is null)
            return null;

        // Set or retrieve attributes as appropriate
        auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;
        if (attrs) {
            clrAttr(pool, bit_i, BlkAttr.ALL_BITS);
            setAttr(pool, bit_i, attrs);
        }
        else
            attrs = getAttr(pool, bit_i);

        void* blk_base_addr = pool.findBase(p);
        size_t blk_size = pool.findSize(p);
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
                void* p2 = malloc(size, attrs, pm_bitmask);
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
                    if (opts.options.mem_stomp)
                        memset(p + size - pm_bitmask_size, 0xF2,
                                blk_size - size - pm_bitmask_size);
                    pool.freePages(pagenum + newsz, psz - newsz);
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
            // if new size is bigger or less than half
            if (blk_size < size || blk_size > size * 2)
            {
                size -= pm_bitmask_size;
                blk_size -= pm_bitmask_size;
                void* p2 = malloc(size, attrs, pm_bitmask);
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
 * min_size beyond its current capacity, up to a maximum of max_size.  This
 * does not attempt to move the memory block (like realloc() does).
 *
 * Returns:
 *  0 if could not extend p,
 *  total size of entire memory block if successful.
 */
private size_t extend(void* p, size_t minsize, size_t maxsize)
in
{
    assert( minsize <= maxsize );
}
body
{
    if (opts.options.sentinel)
        return 0;

    Pool* pool = findPool(p);
    if (pool is null)
        return 0;

    // Retrieve attributes
    auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;
    uint attrs = getAttr(pool, bit_i);

    void* blk_base_addr = pool.findBase(p);
    size_t blk_size = pool.findSize(p);
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
    gc.p_cache = null;
    gc.size_cache = 0;

    if (has_pm) {
        new_size -= size_t.sizeof;
        auto end_of_blk = cast(size_t**)(blk_base_addr + new_size);
        *end_of_blk = pm_bitmask;
    }
    return new_size;
}


//
//
//
private void free(void *p)
{
    assert (p);

    Pool*  pool;
    size_t pagenum;
    Bins   bin;
    size_t bit_i;

    // Find which page it is in
    pool = findPool(p);
    if (!pool)                              // if not one of ours
        return;                             // ignore
    if (opts.options.sentinel) {
        sentinel_Invariant(p);
        p = sentinel_sub(p);
    }
    pagenum = cast(size_t)(p - pool.baseAddr) / PAGESIZE;
    bit_i = cast(size_t)(p - pool.baseAddr) / 16;
    clrAttr(pool, bit_i, BlkAttr.ALL_BITS);

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

        list.next = gc.free_list[bin];
        gc.free_list[bin] = list;
    }
}


/**
 * Determine the allocated size of pointer p.  If p is an interior pointer
 * or not a gc allocated pointer, return 0.
 */
private size_t sizeOf(void *p)
{
    assert (p);

    if (opts.options.sentinel)
        p = sentinel_sub(p);

    Pool* pool = findPool(p);
    if (pool is null)
        return 0;

    auto biti = cast(size_t)(p - pool.baseAddr) / 16;
    uint attrs = getAttr(pool, biti);

    size_t size = pool.findSize(p);
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
        if (p == gc.p_cache)
            return gc.size_cache;

        // Check for interior pointer
        // This depends on:
        // 1) size is a power of 2 for less than PAGESIZE values
        // 2) base of memory pool is aligned on PAGESIZE boundary
        if (cast(size_t)p & (size - 1) & (PAGESIZE - 1))
            return 0;

        gc.p_cache = p;
        gc.size_cache = size - pm_bitmask_size;

        return gc.size_cache;
    }
}


/**
 * Verify that pointer p:
 *  1) belongs to this memory pool
 *  2) points to the start of an allocated piece of memory
 *  3) is not on a free list
 */
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
        pool = findPool(p);
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

                for (list = gc.free_list[bin]; list; list = list.next)
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
        if (p > gc.stack_bottom)
        {
            gc.stack_bottom = p;
        }
    }
    else
    {
        //p = (void *)((uint *)p - 4);
        if (p < gc.stack_bottom)
        {
            gc.stack_bottom = cast(char*)p;
        }
    }
}


/**
 * Retrieve statistics about garbage collection.
 * Useful for debugging and tuning.
 */
private GCStats getStats()
{
    GCStats stats;
    size_t psize = 0;
    size_t usize = 0;
    size_t flsize = 0;

    size_t n;
    size_t bsize = 0;

    for (n = 0; n < gc.pools.length; n++)
    {
        Pool* pool = gc.pools[n];
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
        for (List *list = gc.free_list[n]; list; list = list.next)
            flsize += binsize[n];
    }

    usize = bsize - flsize;

    stats.poolsize = psize;
    stats.usedsize = bsize - flsize;
    stats.freelistsize = flsize;
    return stats;
}

/******************* weak-reference support *********************/

private struct WeakPointer
{
    Object reference;

    void ondestroy(Object r)
    {
        assert(r is reference);
        // lock for memory consistency (parallel readers)
        // also ensures that weakpointerDestroy can be called while another
        // thread is freeing the reference with "delete"
        return locked!(void, () {
            reference = null;
        })();
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
        return locked!(void, () {
            if (wp.reference)
                rt_detachDisposeEvent(wp.reference, &wp.ondestroy);
        })();
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
        return locked!(Object, () {
            return (cast(WeakPointer*)p).reference;
        })();
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


    bool Invariant()
    {
        return true;
    }


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
     * Find base address of block containing pointer p.
     * Returns null if the pointer doesn't belong to this pool
     */
    void* findBase(void *p)
    {
        size_t offset = cast(size_t)(p - this.baseAddr);
        size_t pagenum = offset / PAGESIZE;
        Bins bin = cast(Bins)this.pagetable[pagenum];
        // Adjust bit to be at start of allocated memory block
        if (bin <= B_PAGE)
            return this.baseAddr + (offset & notbinsize[bin]);
        if (bin == B_PAGEPLUS) {
            do {
                --pagenum, offset -= PAGESIZE;
            } while (cast(Bins)this.pagetable[pagenum] == B_PAGEPLUS);
            return this.baseAddr + (offset & (offset.max ^ (PAGESIZE-1)));
        }
        // we are in a B_FREE page
        return null;
    }


    /**
     * Find size of pointer p.
     * Returns 0 if p doesn't belong to this pool if if it's block size is less
     * than a PAGE.
     */
    size_t findSize(void *p)
    {
        size_t pagenum = cast(size_t)(p - this.baseAddr) / PAGESIZE;
        Bins bin = cast(Bins)this.pagetable[pagenum];
        if (bin != B_PAGE)
            return binsize[bin];
        for (size_t i = pagenum + 1; i < this.npages; i++)
            if (this.pagetable[i] != B_PAGEPLUS)
                return (i - pagenum) * PAGESIZE;
        return (this.npages - pagenum) * PAGESIZE;
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



/* ============================ C Public Interface ======================== */


private int _termCleanupLevel=1;

extern (C):

/// sets the cleanup level done by gc
/// 0: none
/// 1: fullCollect
/// 2: fullCollect ignoring stack roots (might crash daemonThreads)
/// result !=0 if the value was invalid
int gc_setTermCleanupLevel(int cLevel)
{
    if (cLevel<0 || cLevel>2) return cLevel;
    _termCleanupLevel=cLevel;
    return 0;
}

/// returns the cleanup level done by gc
int gc_getTermCleanupLevel()
{
    return _termCleanupLevel;
}

void gc_init()
{
    scope (exit) assert (Invariant());
    gc = cast(GC*) cstdlib.calloc(1, GC.sizeof);
    *gc = GC.init;
    initialize();
    version (DigitalMars) version(OSX) {
        _d_osx_image_init();
    }
    // NOTE: The GC must initialize the thread library
    //       before its first collection.
    thread_init();
}

void gc_term()
{
    assert (Invariant());
    if (_termCleanupLevel<1) {
        // no cleanup
    } else if (_termCleanupLevel==2){
        // a more complete cleanup
        // NOTE: There may be daemons threads still running when this routine is
        //       called.  If so, cleaning memory out from under then is a good
        //       way to make them crash horribly.
        //       Often this probably doesn't matter much since the app is
        //       supposed to be shutting down anyway, but for example tests might
        //       crash (and be considerd failed even if the test was ok).
        //       thus this is not the default and should be enabled by
        //       I'm disabling cleanup for now until I can think about it some
        //       more.
        //
        // not really a 'collect all' -- still scans static data area, roots,
        // and ranges.
        return locked!(void, () {
            gc.no_stack++;
            fullcollectshell();
            gc.no_stack--;
        })();
    } else {
        // default (safe) clenup
        return locked!(void, () {
            fullcollectshell();
        })();
    }
}

void gc_enable()
{
    return locked!(void, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        assert (gc.disabled > 0);
        gc.disabled--;
    })();
}

void gc_disable()
{
    return locked!(void, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        gc.disabled++;
    })();
}

void gc_collect()
{
    return locked!(void, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        fullcollectshell();
    })();
}


void gc_minimize()
{
    return locked!(void, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        minimize();
    })();
}

uint gc_getAttr(void* p)
{
    if (p is null)
        return 0;
    return locked!(uint, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        Pool* pool = findPool(p);
        if (pool is null)
            return 0u;
        auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;
        return getAttr(pool, bit_i);
    })();
}

uint gc_setAttr(void* p, uint attrs)
{
    if (p is null)
        return 0;
    return locked!(uint, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        Pool* pool = findPool(p);
        if (pool is null)
            return 0u;
        auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;
        uint old_attrs = getAttr(pool, bit_i);
        setAttr(pool, bit_i, attrs);
        return old_attrs;
    })();
}

uint gc_clrAttr(void* p, uint attrs)
{
    if (p is null)
        return 0;
    return locked!(uint, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        Pool* pool = findPool(p);
        if (pool is null)
            return 0u;
        auto bit_i = cast(size_t)(p - pool.baseAddr) / 16;
        uint old_attrs = getAttr(pool, bit_i);
        clrAttr(pool, bit_i, attrs);
        return old_attrs;
    })();
}

void* gc_malloc(size_t size, uint attrs = 0,
        PointerMap ptrmap = PointerMap.init)
{
    if (size == 0)
        return null;
    return locked!(void*, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        return malloc(size, attrs, ptrmap.bits.ptr);
    })();
}

void* gc_calloc(size_t size, uint attrs = 0,
        PointerMap ptrmap = PointerMap.init)
{
    if (size == 0)
        return null;
    return locked!(void*, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        return calloc(size, attrs, ptrmap.bits.ptr);
    })();
}

void* gc_realloc(void* p, size_t size, uint attrs = 0,
        PointerMap ptrmap = PointerMap.init)
{
    return locked!(void*, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        return realloc(p, size, attrs, ptrmap.bits.ptr);
    })();
}

size_t gc_extend(void* p, size_t min_size, size_t max_size)
{
    return locked!(size_t, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        return extend(p, min_size, max_size);
    })();
}

size_t gc_reserve(size_t size)
{
    if (size == 0)
        return 0;
    return locked!(size_t, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        return reserve(size);
    })();
}

void gc_free(void* p)
{
    if (p is null)
        return;
    return locked!(void, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        free(p);
    })();
}

void* gc_addrOf(void* p)
{
    if (p is null)
        return null;
    return locked!(void*, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        Pool* pool = findPool(p);
        if (pool is null)
            return null;
        return pool.findBase(p);
    })();
}

size_t gc_sizeOf(void* p)
{
    if (p is null)
        return 0;
    return locked!(size_t, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        return sizeOf(p);
    })();
}

BlkInfo gc_query(void* p)
{
    if (p is null)
        return BlkInfo.init;
    return locked!(BlkInfo, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        return getInfo(p);
    })();
}

// NOTE: This routine is experimental.  The stats or function name may change
//       before it is made officially available.
GCStats gc_stats()
{
    return locked!(GCStats, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        return getStats();
    })();
}

void gc_addRoot(void* p)
{
    if (p is null)
        return;
    return locked!(void, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        if (gc.roots.append(p) is null)
            onOutOfMemoryError();
    })();
}

void gc_addRange(void* p, size_t size)
{
    if (p is null || size == 0)
        return;
    return locked!(void, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        if (gc.ranges.append(Range(p, p + size)) is null)
            onOutOfMemoryError();
    })();
}

void gc_removeRoot(void* p)
{
    if (p is null)
        return;
    return locked!(void, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        bool r = gc.roots.remove(p);
        assert (r);
    })();
}

void gc_removeRange(void* p)
{
    if (p is null)
        return;
    return locked!(void, () {
        assert (Invariant()); scope (exit) assert (Invariant());
        bool r = gc.ranges.remove(Range(p, null));
        assert (r);
    })();
}

void* gc_weakpointerCreate(Object r)
{
    // weakpointers do their own locking
    return weakpointerCreate(r);
}

void gc_weakpointerDestroy(void* wp)
{
    // weakpointers do their own locking
    weakpointerDestroy(wp);
}

Object gc_weakpointerGet(void* wp)
{
    // weakpointers do their own locking
    return weakpointerGet(wp);
}


// vim: set et sw=4 sts=4 :
