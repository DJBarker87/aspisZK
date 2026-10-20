# Stage-2 refactor (2026-10-20)

VERIFIER SOURCE CHANGE under LEAD-DECISION-STAGE2-REFACTOR-20261020.
Final Rust source: `2ec37343acfb1b857cbec6569ad3175930a962bb`.
Pinned Charon and Aeneas now translate the whole stage-2 cone successfully.
The prior failed source and measurements remain historical in
`../evidence/stage2-refactor-extraction-20261020/REPORT.md`.
Current report, all attempts and pins:
`../evidence/stage2-continuation-20261020/REPORT.md`.

## Repair

The old span description was wrong: candidate.rs:237:20–22 (zero-based
columns) identifies `&v`, not `&a`. Constructing the relation View after the
query loop avoids reborrowing the View whose folded-root field had been used.
The early inactive decoder and folded-root Merkle authentication are retained.
The late View supplies the three fields actually read by finish_relation;
its unused folded_root is None. Moving/reconstructing the accumulator remains
safe source structure but was not the original failing loan.

Whole-cone extraction then exposed further joins in Reader/cursor loops,
root/query accesses, batch sorting, Merkle scratch state, residue updates,
geometry and query accumulation. Concrete helpers isolate those loans. The
query loop carries an owned Result state; its successful query returns the
next accumulator and pending weights. Three explicit ordered Merkle calls
reuse borrowed scratch arrays. Arithmetic, byte layouts and digest inputs
retain their definitions; exact runtime comparisons are supplied separately.

Checkpoint query reads are explicit and ordered. Ten semantic-alpha reads
use a separate concrete helper so the emitted resume body stays below the
pinned pretty-printer indentation limit. Reader::k is inlined for CU. The
original four-limb residue loops run inside an isolated row helper with
transparent getters; this avoids both the translator's nested loan failure
and the measured cost of forced unrolling. The optional legacy accumulator
and historical eight-way source remain available to audit builds.

The extraction starts at the actual crate's tx2_authenticated. Orchestration,
resume, parsing, query loops, accumulation, relation and Merkle bodies remain
concrete. Arithmetic/heap/hash/weights/domain/dot/pairing/trace methods are
explicit backend frontiers. Only required field/point data layouts cross
those opaque boundaries; no synthetic orchestration is substituted.

## Verification and artifacts

Codec 1,233; ordered traces; checkpoint/program, crate and Pool suites;
proof-size teeth; strict/authenticated path; complete-linked-ELF stack audit;
and all six per-fixture B1 CU criteria pass on the final source. The optimized
P_R1 gate accepts and strictly/densely verifies 8/8; its separate retry loop
accepts and verifies in one attempt. All 21 final-source gate receipts exit 0.

ELF SHA-256:
`9672cc4842d478313293133f5597e8da5a352842f2fbf96371b5fa189fe0f16a`
(1,506,920 bytes). LLBC SHA-256:
`4c36344e1de0f90dfa074fc35a0664408b4f258a11c72617d7a0241fd6aa3182`
(7,009,222 bytes, has_errors=false). Raw generated Lean and all source/tool
pins are committed; executable and LLBC binaries remain on the build host.

Nine focused local modules support the first three shape facts: fixed parse
length, successful resume proof-rehash equality with checkpoint bytes 16..48
under byte-comparison soundness, and twelve ordered query calls from 10 to 22.
The last fact derives the increment from complete emitted query/accumulation
bodies with typed backend operations universally quantified. All successful
axioms audits use only propext, Classical.choice and Quot.sound. Mechanical
bindings connect these complete bodies to the final raw emission; raw
external templates are pinned, not accepted as proof assumptions.

## Open

Concrete backend instantiation/correspondence and full source/model/Checks
refinement (R13/R12); arithmetic and Merkle correctness; authenticated
checkpoint provenance and skipped-value canonicality (R15); all-input
oracle/first-read bounds (R19); deployment/release-certificate correspondence
and analytical CU bounds (S8). The ELF itself is pinned here. Fixture CU
margins are small (minimum 201 CU settlement, 281 CU stage 1); these
measurements do not prove an all-input budget. Whole-cone emission is not a
backend-complete Lean verification package or universal source equivalence.
