#!/bin/bash
# Test of fv_round_outcomes.sh (the outcome comparison of fv_round_checks.sh) on recorded outcome lists.
# base: the frozen gate frz/c1. out: round 2b (aspis-next 8ba85f1946b). neg1..neg4: planted failures made from out.
# Expected: case 1 bad=0; cases 2 to 6 bad=1.
H=$(cd "$(dirname "$0")/.." && pwd); F=$(cd "$(dirname "$0")" && pwd)
run() { # dir removals
  local OUT=$(mktemp -d); cp $F/$1/program-tests-*.outcomes $OUT/; local ST=$OUT/steps.txt; : > $ST; local bad=0
  note() { echo "$*" >> $ST; }
  REMOVALS=$2; source $H/fv_round_outcomes.sh
  cmp_outcomes "program tests (deployed)" deployed $OUT/program-tests-deployed.outcomes $F/base/program-tests-deployed.outcomes
  cmp_outcomes "program tests (two-transaction)" two-transaction $OUT/program-tests-two-transaction.outcomes $F/base/program-tests-two-transaction.outcomes
  lp=$(check_listed_pass); echo "$lp" | grep -q "DOES NOT PASS" && bad=1
  echo $bad; rm -rf $OUT
}
L=$H/fv_round_intended_removals.tsv; fail=0
check() { local got=$(run $2 $3); if [ "$got" = "$4" ]; then echo "case $1: bad=$got (expected $4) ok"; else echo "case $1: bad=$got (expected $4) WRONG"; fail=1; fi; }
check 1 out "$L" 0                # the real round with the list: passes
check 2 out /dev/null 1           # the real round without the list: two absent tests not listed
check 3 neg1 "$L" 1               # a base test changes outcome
check 4 neg2 "$L" 1               # a listed test fails where it should still run
check 5 neg3 "$L" 1               # a listed test reappears where it was removed
check 6 neg4 "$L" 1               # an unlisted base test is absent
exit $fail
