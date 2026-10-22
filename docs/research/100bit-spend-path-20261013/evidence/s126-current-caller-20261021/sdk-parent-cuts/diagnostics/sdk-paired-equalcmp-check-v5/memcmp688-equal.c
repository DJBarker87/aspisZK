#include <stddef.h>
int memcmp(const void *, const void *, size_t);
__CPROVER_bool __CPROVER_same_object(const void *, const void *);
__CPROVER_bool __CPROVER_array_equal(const void *, const void *);
void __CPROVER_array_copy(void *, const void *);
void __CPROVER_assert(__CPROVER_bool, const char *);
/* Every specialization precondition is ASSERTED by the caller. The fixed688
   equal-array/no-write leaf is checked separately. Other sizes call the
   unchanged original memcmp; calls inside this newly linked body are not
   affected by the earlier call-replacement pass. */
int s126_memcmp688_equal(const void *left, const void *right, size_t length) {
  if(length != 688) return memcmp(left, right, length);
  __CPROVER_assert(__CPROVER_r_ok(left,688) && __CPROVER_r_ok(right,688),
                   "specialized memcmp has two readable688-byte regions");
  __CPROVER_assert(left == right || !__CPROVER_same_object(left,right),
                   "specialized memcmp matches checked same-start/distinct-object leaf");
  /* array_equal compares whole root arrays, so pointer casts alone do not
     establish a 688-byte view of a larger source allocation. array_copy into
     fixed local arrays creates the two exact views before equality testing. */
  unsigned char left_bytes[688], right_bytes[688];
  __CPROVER_array_copy(left_bytes,left);
  __CPROVER_array_copy(right_bytes,right);
  __CPROVER_assert(__CPROVER_array_equal(left_bytes,right_bytes),
                   "specialized memcmp caller establishes all688 equal bytes");
  return 0;
}
