#include <stddef.h>
#include <stdint.h>
#include <errno.h>
#include <string.h>
static uint32_t probes, draws;
long getrandom(void *p, size_t n, unsigned int flags) {
    (void)flags;
    if (!n) { ++probes; return 0; }
    ++draws;
    memset(p, 0xa5, n);
    errno = EIO;
    return -1;
}
uint64_t pv_dispatch_counts(void) { return ((uint64_t)probes<<32)|draws; }
