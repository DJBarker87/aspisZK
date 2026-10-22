#include <stddef.h>
int s126_entry_memcmp(const void *,const void *,size_t);
int (*s126_keep_entry_declaration)(const void *,const void *,size_t)=s126_entry_memcmp;
