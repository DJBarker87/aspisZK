#include <stddef.h>
int s126_coupled_memcmp(const void *,const void *,size_t);
int (*s126_keep_comparison)(const void *,const void *,size_t)=s126_coupled_memcmp;
