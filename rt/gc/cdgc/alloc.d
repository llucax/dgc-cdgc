/**
 * This module contains allocation functions for the garbage collector.
 *
 * Copyright: Copyright (C) 2005-2006 Digital Mars, www.digitalmars.com.
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

module rt.gc.cdgc.alloc;

version (Win32)
    import tango.sys.win32.UserGdi;
else version (Posix)
    import tango.stdc.posix.sys.mman;
else
    import tango.stdc.stdlib;


// Public interface/Documentation

version (D_Ddoc) {

/**
 * Map memory.
 */
void* os_mem_map(size_t nbytes);

/**
 * Unmap memory allocated with os_mem_map().
 * Returns:
 *      true  success
 *      false failure
 */
bool os_mem_unmap(void* base, size_t nbytes);

}

// Implementations
else static if (is(typeof(VirtualAlloc))) {
    void* os_mem_map(size_t nbytes)
    {
        return VirtualAlloc(null, nbytes, MEM_RESERVE | MEM_COMMIT,
                PAGE_READWRITE);
    }

    bool os_mem_unmap(void* base, size_t nbytes)
    {
        return VirtualFree(base, 0, MEM_RELEASE) != 0;
    }
}

else static if (is(typeof(mmap)) && is(typeof(MAP_ANON))) {
    void* os_mem_map(size_t nbytes)
    {
        void* p = mmap(null, nbytes,
                PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
        return (p == MAP_FAILED) ? null : p;
    }

    bool os_mem_unmap(void* base, size_t nbytes)
    {
        return munmap(base, nbytes) == 0;
    }
}

else static if (is(typeof(malloc))) {
    // NOTE: This assumes malloc granularity is at least (void*).sizeof.  If
    //       (req_size + PAGESIZE) is allocated, and the pointer is rounded up
    //       to PAGESIZE alignment, there will be space for a void* at the end
    //       after PAGESIZE bytes used by the GC.

    import rt.gc.cdgc.gc: PAGESIZE;

    const size_t PAGE_MASK = PAGESIZE - 1;

    void* os_mem_map(size_t nbytes)
    {
        byte* p, q;
        p = cast(byte* ) malloc(nbytes + PAGESIZE);
        q = p + ((PAGESIZE - ((cast(size_t) p & PAGE_MASK))) & PAGE_MASK);
        *cast(void**)(q + nbytes) = p;
        return q;
    }

    bool os_mem_unmap(void* base, size_t nbytes)
    {
        free(*cast(void**)(cast(byte*) base + nbytes));
        return true;
    }
}

else static assert(false, "No supported allocation methods available.");


// vim: set et sw=4 sts=4 :
