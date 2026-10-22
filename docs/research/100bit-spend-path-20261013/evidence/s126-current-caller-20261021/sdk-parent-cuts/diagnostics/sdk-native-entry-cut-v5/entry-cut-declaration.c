#include <stddef.h>
int s126_entry_memcmp(const void *,const void *,size_t);
int (*s126_keep_entry_declaration)(const void *,const void *,size_t)=s126_entry_memcmp;
size_t s126_havoc_input(unsigned char *,size_t);
size_t (*s126_keep_initializer)(unsigned char *,size_t)=s126_havoc_input;
