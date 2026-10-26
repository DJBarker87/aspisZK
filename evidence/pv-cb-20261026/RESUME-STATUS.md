# Resume status

Branch `codex/pv-cb-20261026`, resume base `c0e2f7af57`. **Target not yet established.** Work is awaiting restoration of the shared build-host workspace, not budget exhaustion.

Before:73 assigned rows,30 value interpretations,0 discharged current-source equations. After:18 source/value rows ROW-DISCHARGED(candidate),55 not discharged;0 ledger rows or privacy-endpoint premises removed. The full op→row→status→theorem→receipt table is [RESUME-SOURCE-ROWS.md](RESUME-SOURCE-ROWS.md). No new axioms, canonicality, or primitive-totality hypotheses were added to these source equations.

The18 supplied candidate laws are ops3,71,72,77,80,82,83,86,100,101,110,111,114,127,128,130,131,229. Zeroizing equations are value-only; erasure/fence/Drop effects remain deferred. The source-body and carrier proofs are supported by the numbered receipts. [RESUME-LOCAL-EVIDENCE-AUDIT.json](RESUME-LOCAL-EVIDENCE-AUDIT.json) verifies that every accepted row still has a green receipt, the named theorem in its axioms output, and a matching current source hash. It is a local evidence audit, not a Lean dependency-closure replay.

op117 remains PARTIAL: prepared root equality and fill induction compile; six no-stub native step/helper gates pass. Full mirror, combined Horner, uniform-coefficient Horner, and power-chain gates timed out. Fresh actual root extraction reaches Charon but Aeneas fails at loop join/collapse (`InterpReduceCollapse.ml1991`). Details: [MASK-STEPS-RESUME.md](MASK-STEPS-RESUME.md). No timeout is a counterexample or pass.

The later pure attempts retain exact local obstructions:26 opaque private `_join`;31 unsupported str→slice transmute;32/81 allocator-parametric Vec type;79 loop join/collapse. Other pure obstructions are in the table; none is replaced by a native-composition deferral.

71/100 Lean attempts ran (60 green,11 failed);10/20 Kani runs ran (6 pass,4 timeout). ID24071 did not launch and is uncharged. Last actual compile24070 failed on a generated shift-count type. Its correction and final Op105Exact equation are PREPARED, not checked. The shared paths then vanished; [HOST-PATH-LOSS-20261026.md](HOST-PATH-LOSS-20261026.md) records the exact errors and limited24070 receipt provenance. The combined18-row dictionary, five projection groups and final audit are also PREPARED only.

No shipped source under crates/programs changed; no push/merge, wallet or key action. Four admission-wait deviations are recorded transparently in [reservation-cadence-deviations.json](reservation-cadence-deviations.json); caps and the standing scanner were retained.

Next: restore the retained shared cache; compile corrected Op105Funs using next unused ID24072, then Op105Exact; continue107,109,118 and check the combined candidate, focused projection groups and final axioms/dependency audit with the remaining29 Lean and10 Kani budget.

Commits since resume base (before this checkpoint commit):

```text
392f50c711 Prove fresh write phi and wide-negation laws and retain generic heap obstruction
3d8df8ed61 Prove fresh parser source law and record mask and storage extraction obstructions
1893701f76 Prove prepared mask root by fill induction and record bounded source-step checks
1db675d834 Record weights and pole source extraction obstructions without effect deferrals
575f9d5b9b Install extracted public-statement equality with bijective carrier transport
93c41a0ab2 Record direct statement helper extraction results and preserve transition source ownership
6856c9a6cf Record generic SHA source gaps and prove the associated-carrier model obstruction
1995624572 Record statement and SHA extraction failures without claiming pure-row discharge
90896ab747 Correct source-law provenance counts and record candidate extraction obstructions
b66b0c325f Prove extracted Zeroizing value laws and retain effect deferrals
7168803f2c Install extracted embedding and context comparison with source constant and points equations
88955e0c83 Discharge field negation and inverse source callback equations
3cc9b2873c Prove heap and Merkle constant source equations and isolate leaf wrapper emission gap
fd16f6c317 Discharge codec clone and phi callback rows against extracted definitions
9e47d9c059 Record focused shipped Vec extraction failures and next proof route
3a16c923fd Prove take callback against direct shipped extraction and record path obstructions
```
