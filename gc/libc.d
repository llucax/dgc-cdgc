
module gc.c;

version (Windows) {
    alias int   c_long;
    alias uint  c_ulong;
}
else {
    static if ((void*).sizeof > int.sizeof) {
        alias long c_long;
        alias ulong c_ulong;
    }
    else {
        alias int c_long;
        alias uint c_ulong;
    }
}

// C standard library
extern (C):
void* realloc(void*, size_t);
void* malloc(size_t);
void* calloc(size_t, size_t);
void free(void*);
void* memset(void*, int, size_t);
void* memcpy(void*, void*, size_t);
void* memmove(void*, void*, size_t);
void printf(char* fmt, ...);

