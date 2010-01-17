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

module gc.alloc;


// C OS-specific API

private extern (C) {
    version (Win32) {
        alias void* POINTER;
        alias POINTER LPVOID;
        alias uint DWORD;
        alias int WINBOOL;
        enum: DWORD {
            PAGE_READWRITE = 4,
            MEM_RESERVE = 8192,
            MEM_COMMIT = 4096,
            MEM_DECOMMIT = 16384,
            MEM_RELEASE = 32768,
        }
        LPVOID VirtualAlloc(LPVOID, DWORD, DWORD, DWORD);
        WINBOOL VirtualFree(LPVOID, DWORD, DWORD);
    }
    else version (Posix) {
        version (linux) enum: bool { OPTIONAL_LARGEFILE_SUPPORT = true }
        else version (solaris) enum: bool { OPTIONAL_LARGEFILE_SUPPORT = true }
        else enum: bool { OPTIONAL_LARGEFILE_SUPPORT = false }
        static if (OPTIONAL_LARGEFILE_SUPPORT)
            enum: bool { USE_LARGEFILE64 = ((void*).sizeof == 4) }
        else
            enum: bool { USE_LARGEFILE64 = false }
        static if (USE_LARGEFILE64 || (void*).sizeof > int.sizeof)
            alias long off_t;
        else
            alias int off_t;
        enum: int {
            PROT_NONE = 0x0,
            PROT_READ = 0x1,
            PROT_WRITE = 0x2,
            PROT_EXEC = 0x4,
            MAP_SHARED = 0x01,
            MAP_PRIVATE = 0x02,
            MAP_FIXED = 0x10,
        }
        const MAP_FAILED = cast(void*) -1;
        // Non-standard, but needed
        version (linux) { enum: int { MAP_ANON = 0x20 } }
        else version (darwin) { enum: int { MAP_ANON = 0x1000 } }
        else version (freebsd) { enum: int { MAP_ANON = 0x1000 } }
        else version (solaris) { enum: int { MAP_ANON = 0x100 } }
        void* mmap(void*, size_t, int, int, int, off_t);
        int munmap(void*, size_t);
    }
    else {
        // Standard C library
        import gc.libc;
    }
}


// Public interface

version (D_Ddoc)
{
    /**
     * Map memory.
     */
    void* os_mem_map(size_t nbytes);

    /**
     * Commit memory.
     * Returns:
     *      true  success
     *      false failure
     */
    int os_mem_commit(void* base, size_t offset, size_t nbytes);

    /**
     * Decommit memory.
     * Returns:
     *      true  success
     *      false failure
     */
    int os_mem_decommit(void* base, size_t offset, size_t nbytes);

    /**
     * Unmap memory allocated with os_mem_map().
     * Memory must have already been decommitted.
     * Returns:
     *      true  success
     *      false failure
     */
    int os_mem_unmap(void* base, size_t nbytes);
}
// Implementations
else static if (is(typeof(VirtualAlloc)))
{
    void* os_mem_map(size_t nbytes)
    {
        return VirtualAlloc(null, nbytes, MEM_RESERVE, PAGE_READWRITE);
    }

    int os_mem_commit(void* base, size_t offset, size_t nbytes)
    {
        void* p = VirtualAlloc(base + offset, nbytes, MEM_COMMIT, PAGE_READWRITE);
        return cast(int)(p is null);
    }

    int os_mem_decommit(void* base, size_t offset, size_t nbytes)
    {
        return cast(int)(VirtualFree(base + offset, nbytes, MEM_DECOMMIT) == 0);
    }

    int os_mem_unmap(void* base, size_t nbytes)
    {
        return cast(int)(VirtualFree(base, 0, MEM_RELEASE) == 0);
    }
}
else static if (is(typeof(mmap)) && is(typeof(MAP_ANON)))
{
    void* os_mem_map(size_t nbytes)
    {
        void* p = mmap(null, nbytes,
                PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
        return (p == MAP_FAILED) ? null : p;
    }

    int os_mem_commit(void* base, size_t offset, size_t nbytes)
    {
        return 0;
    }

    int os_mem_decommit(void* base, size_t offset, size_t nbytes)
    {
        return 0;
    }

    int os_mem_unmap(void* base, size_t nbytes)
    {
        return munmap(base, nbytes);
    }
}
else static if (is(typeof(malloc)))
{
    // NOTE: This assumes malloc granularity is at least (void*).sizeof.  If
    //       (req_size + PAGESIZE) is allocated, and the pointer is rounded up
    //       to PAGESIZE alignment, there will be space for a void* at the end
    //       after PAGESIZE bytes used by the GC.

    import gcx; // for PAGESIZE

    const size_t PAGE_MASK = PAGESIZE - 1;

    void* os_mem_map(size_t nbytes)
    {
        byte* p, q;
        p = cast(byte* ) malloc(nbytes + PAGESIZE);
        q = p + ((PAGESIZE - ((cast(size_t) p & PAGE_MASK))) & PAGE_MASK);
        *cast(void**)(q + nbytes) = p;
        return q;
    }

    int os_mem_commit(void* base, size_t offset, size_t nbytes)
    {
        return 0;
    }

    int os_mem_decommit(void* base, size_t offset, size_t nbytes)
    {
        return 0;
    }

    int os_mem_unmap(void* base, size_t nbytes)
    {
        free(*cast(void**)(cast(byte*) base + nbytes));
        return 0;
    }
}
else
{
    static assert(false, "No supported allocation methods available.");
}
