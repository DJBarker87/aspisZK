#!/bin/bash
# Sourced by fv_round_checks.sh (and by its test harness). Comparison of program-test outcome lists against the
# base, with a list of intended removals. Needs: OUT (result directory), REMOVALS (path or empty), note(), bad.
# outcome lists: every test of the base keeps its outcome; absent base tests must be exactly the intended removals
export LC_ALL=C   # one collation for every sort and comm below (and on any machine the harness runs on)
outcomes() { grep -E "^test .* (ok|FAILED|ignored)$" "$1" | sort; }
if [ -n "$REMOVALS" ]; then cp "$REMOVALS" $OUT/intended-removals.tsv; else : > $OUT/intended-removals.tsv; fi
note "intended removals: $(grep -vc '^#\|^$' $OUT/intended-removals.tsv) listed ($OUT/intended-removals.tsv)"
listed() { awk -F'\t' -v c="$1" '!/^#/ && NF>=4 && $2==c {print $1}' $OUT/intended-removals.tsv | sort -u; }
cmp_outcomes() { # label, configuration name, round outcomes file, base outcomes file
  local names_r=$(mktemp) names_b=$(mktemp) lr=$(mktemp) lb=$(mktemp)
  sort -u $3 > $lr; sort -u $4 > $lb; set -- "$1" "$2" $lr $lb       # sorted copies, same collation
  awk '{print $2}' $3 | sort -u > $names_r; awk '{print $2}' $4 | sort -u > $names_b
  local missing=$(comm -13 $names_r $names_b)                       # base tests absent from the round
  local changed=$(comm -13 <(cat $3) <(cat $4) | awk '{print $2}' | sort -u | comm -12 - $names_r | wc -l)   # present on both sides, outcome differs
  local unlisted=$(comm -23 <(printf '%s\n' $missing | sed '/^$/d' | sort -u) <(listed $2) | wc -l)
  local reappeared=$(comm -12 $names_r <(listed $2) | wc -l)
  local added=$(comm -23 $names_r $names_b | wc -l)
  local addfail=$(comm -23 <(cat $3) <(cat $4) | grep 'FAILED$' | awk '{print $2}' | sort -u | comm -23 - $names_b | wc -l)
  note "$1: $(wc -l < $3) tests, $(grep -c 'FAILED$' $3) failing; base tests with a changed outcome $changed; base tests absent $(printf '%s\n' $missing | sed '/^$/d' | wc -l) (not on the intended-removals list: $unlisted); listed tests present here $reappeared; tests only in the round $added (failing $addfail)"
  for t in $missing; do note "   absent: $t$(listed $2 | grep -qx "$t" && echo ' (intended)' || echo ' (NOT LISTED)')"; done
  [ $((changed)) -eq 0 ] && [ $((unlisted)) -eq 0 ] && [ $((reappeared)) -eq 0 ] && [ $((addfail)) -eq 0 ] || bad=1
  rm -f $names_r $names_b $lr $lb
}
check_listed_pass() { # every listed test must pass in the configuration where it still runs
  awk -F'\t' '!/^#/ && NF>=4 {print $1"\t"$4}' $OUT/intended-removals.tsv | while IFS=$'\t' read -r t c; do
    f=$OUT/program-tests-$c.outcomes
    if grep -qxF "test $t ... ok" $f; then echo "   listed test passes where it still runs: $t ($c)"; else echo "   LISTED TEST DOES NOT PASS where it should run: $t ($c)"; fi
  done
}
