Withdrawal validator: exact-source cut and checked Lean 4.31 helper

Base 953b7a55fdab799564b963060e4d9edc0d5545da. The sole production edit
replaces digest_is_canonical's fixed Digest iterator.all with eight ordered
scalar < P comparisons; signature, inline attribute and validation error order
are unchanged. production/ retains full before/after files, patch and hashes.
The changed source SHA256 is 0fedd7579aba09b67415f7f7f5e18942643444e1570af25ec7db76510ec57a35.

The new withdrawal-validation-extraction-kit copies fourteen exact declarations
and their attributes into a dependency-free namespace layout. Its source-manifest
pins original file/revision hashes and byte spans; --check verifies body identity.
Native differential tests compare the retained original predicate and complete
validator results across each of eight coordinates at 0,1,P-1,P,u32::MAX, with
canonical backgrounds 0/P-1, amount boundaries and earlier/later error cases.
The two differential tests passed (2.449 s; 198,528 KiB sampled RSS), as did the
existing exact_statement_encodings_roundtrip_and_pin_zero_fee test (80.934 s;
960,640 KiB) and conservation_range_destination_and_overflow_attacks_reject
(4.437 s; 75,664 KiB). The release cache was reused; only aspis-statement rebuilt.

Both failed original-source extraction attempts remain separate under extraction/.
Attempt A's tools exited zero but the runner rejected opaque slice Iter::all.
Attempt B included the exact pinned nightly all body; Charon passed but Aeneas
failed on non-ADT Iter expansion. analysis/ preserves that body/source and LLBC
metadata. Neither attempt is accepted proof evidence or imported by final proofs.
Attempt C uses the actual eight-check production helper: Charon 0.891 s/204,400 KiB,
Aeneas 1.035 s/73,504 KiB, both exit zero, no opaque functions. Source cuts,
commands, tool hashes, generated source and translation metadata are retained.
Binary/source correspondence of the extraction tools is not independently proved.

Accepted declarations, namespace AspisR1WithdrawalValidation.Amount431:
- success_amount_guard: actual generated withdrawal validator p = ok (.Ok ())
  implies 0 < p.amount.val and p.amount.val < 2^30. No fabricated caller premise
  or assumed common success; earlier errors are inverted from actual execution.
- success_nonzero: the same premise implies amount.val is not zero.
- digest_make: the exact result for eight symbolic words is ok of their canonical
  conjunction's Boolean decision.
- digest_success_iff: for any Array M31 8, generated predicate = ok true iff
  every member of its underlying list has value < 2147483647.
These are helper facts, not a proof of source caller reachability.

Three focused Lean 4.31 checks passed using retained backend objects:
Types 16.709 s/2,810,528 KiB; Funs 4.169 s/2,802,368 KiB; helper proof
15.199 s/2,784,160 KiB. All process swap counts were zero. System swap was
preexisting, unchanged or decreased, and recorded in receipts. Eight #print axioms
reports (three generated functions and five helper declarations) contain only
propext, Classical.choice and Quot.sound. One unused-simp warning is retained.
lean/final-green and lean/axioms.json carry the evidence; objects are optional
cache artifacts. Backend source/object reference pins were rechecked; toolchain
version and all pinned runtime dylibs were observed and hashed again.

Every extraction command used a sampled 3 GiB process-group stop and 180 s timeout;
native/Lean checks used sampled 7 GiB stop and 180 s timeout, with Lean -M6000.
These are sampled guards, not hard cgroups. No build-host or cold backend build.
The run wrappers retain original absolute paths; adapt only paths when replaying.

OPEN: extraction/compiler/runtime semantics, extracted caller-to-helper transport,
fixed mapping between separately extracted public carriers, ASF8/ASWP and late
record codecs, account/checkpoint/hash/custody binding, and single-toolchain
integration with Lean 4.32. The caller inventory is separately pinned to the
pre-refactor coordinator revision in J1-PUBLIC-CALLER-BOUNDARY-20261015.txt.
No full J1.a or arbitrary SourceValidationAmountGuard closure is claimed.

Whitespace check passes for production, proof, kit and authored notes. Retained
raw generated template/log/patch artifacts keep their original whitespace, so
a repository-wide diff --check reports only those evidence bytes.
