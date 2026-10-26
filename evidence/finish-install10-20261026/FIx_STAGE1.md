# Stage 1: native ordered high sums

FIx_ArithmeticTotal.add/mul give canonical native forward success and exact
field values. FIx_HighSumInner.value and FIx_HighSumOuter.value prove the
actual installed inner/outer loops, including unchanged selector carrier and
ordered accumulator. FIx_HighSum.source/value compose the actual native caller.
No bounded-candidate implementation is substituted. Native high-array
canonicality and bounded ranges are explicit local hypotheses, to be derived
from the actual boxed selectors at composition. No top premise is discharged.

Passing receipts:001,005,008,010. Errors:002–004 read/iterator simplification;
006–007 outer iterator proof/notation/abbreviation;009 introspection names
were invalid (the coefficient lemmas themselves printed standard axioms).
All failures are retained and excluded. No timeout, memory kill, cap increase,
unchanged rerun, dependency build, Kani, Rust or shipped-source edit.
All new proven theorems print only standard axioms. Each receipt includes
command,revision,dirty snapshot hash,deps fingerprint,exit,wall,RSS,swap,cgroup.
