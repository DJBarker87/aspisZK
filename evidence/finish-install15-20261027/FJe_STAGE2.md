# Stage 2: raw-harness diagnosis and reference algebra

FJe_002 checks packing additivity and the source ordered sum on arbitrary
same-operand field functions. Axioms [propext,Quot.sound]. This is algebra,
not source refinement or deployed closure. FJe_001 failed because the inherited
R0P definition requires Field rather than CommRing; corrected before002.
FJe_003 failed on reserved identifier `local`; corrected to localRows.
Both failed logs are excluded from proof credit; compiler-generated sorryAx
reports in failed attempts are not accepted theorems or source admissions.

FJe_K002 isolated local raw packing: exit1,87.83327947900398s,
peak6116528KiB,swap0. 1/794 failed (memcmp unwind),793 undetermined,
0/1 covers satisfied (undetermined). Array equality introduced a32-byte
memcmp outside the intended four-element loop bound6. No semantic mismatch
was found or ruled out. FJe_K003 changes the source harness to compare all
four u64 outputs individually; no memcmp,larger cap or disabled check.
Complete external/leading/full harnesses now also compare scalar limbs.
Future solver scratch is confined to this job's own solver-temp directory.

No shipped source or dictionary changed. No reference bridge is assumed.
Budgets at stage edit:3/100 Lean,3/20 Kani (third running).
