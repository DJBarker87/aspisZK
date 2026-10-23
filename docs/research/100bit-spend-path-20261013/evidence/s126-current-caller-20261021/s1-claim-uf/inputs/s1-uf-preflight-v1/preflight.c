#include <stdint.h>
extern uint64_t __CPROVER_uninterpreted_aspis_word(uint64_t,uint64_t);
extern _Bool __CPROVER_uninterpreted_aspis_flag(uint64_t,uint64_t);
extern uint64_t nondet_u64(void);
int main(void) {
 uint64_t a=nondet_u64(),b=nondet_u64();
 __CPROVER_assume(a==b);
 __CPROVER_assert(__CPROVER_uninterpreted_aspis_word(7,a)==__CPROVER_uninterpreted_aspis_word(7,b),"word functional consistency");
 __CPROVER_assert(__CPROVER_uninterpreted_aspis_flag(7,a)==__CPROVER_uninterpreted_aspis_flag(7,b),"flag functional consistency");
#ifdef NEGATIVE
 __CPROVER_assert(__CPROVER_uninterpreted_aspis_word(7,a)==a,"negative control: arbitrary function need not be identity");
#endif
 return 0;
}
