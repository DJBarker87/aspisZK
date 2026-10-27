# Sampler diagnostic — 2026-10-27

No premise removed. S2/A2 and the 100-bit target remain open.

## Q1 Native
Frozen source revision `4bb3b3f51e16b4525f1d10336e2b0bcbbd775387`, scratch-only cfg(test) wrapper, `cargo test --release --locked --offline -j4`. SDX_R003 passed.

| Block | Digits | Quotient |
|---|---|---|
| P | [0,1,0,0,0,0,0,0] | 0 |
| zero | [0,0,0,0,0,0,0,0] | 0 |
| P+1 | [1,1,0,0,0,0,0,0] | 0 |
| 32 ff | [255,2048,7168,14336,17920,14336,7168,2048] | 256 |

Graph validated against frozen Cargo.lock before each test launch; offline and lock hash unchanged (SDX_graph.json, SDX_lock.json). R001 failed before compilation because c3 path source was not yet copied; R002 failed on scratch println without std qualification; R003 corrects that wrapper. No timeout or memory kill.

## Q2 Emitted
The phrase “the SAME function of the adopted release extraction” has a provenance obstruction. The manifest `docs/research/100bit-spend-path-20261013/design/D188-PROVENANCE-FINDING-20261027.md` and the trust appendix select **AspisR1PublicPreparation.Funs**, an adapted historical cohort, at:

`docs/research/100bit-spend-path-20261013/lean-candidates/s1-prepared-claim-carrier-bridge-20261020/sources/AspisR1PublicPreparation/Funs.lean`

SHA256 `544b75b962ade326ff1069b6986805a175cc90db1c592b1c524dffcd94693d2d`. It imports Aeneas and Types, **no FunsExternal**, and contains **no low_base_p_digits definition**. Therefore four concrete Results for that nonexistent declaration cannot honestly be supplied. This is a precise obstruction to Q2's requested attribution, not a substituted proof.

The actual indexed sampler dependency in the coherent/adopted proof cohort is `AspisR1Post25Sampler.Funs`, from:

`docs/research/100bit-spend-path-20261013/lean-candidates/post25-ordinary-sample-candidate-20261020/sanitized-sources/Funs.lean`

source SHA256 `f02a8fc4503304c2630052a116be257ef507780ffe166844e1b08d71e0e9ec11`; object SHA256 `4fc184f23d7427726cf8dee25e77792736ae508a252c799523d73bbbaee894ad`, matching SInt2's selected object manifest. It imports Aeneas and Types, **no FunsExternal**. Its own extraction manifest calls its source a candidate-only indexed sampler; its loop explicitly stores each quotient. `SDX_cohort_pin.json` records that association without promoting the candidate source to frozen Rust.

`SDX_Cohort.resultP/resultZero/resultP1/resultFF` (L032) prove its complete Results equal the Q1 table, using inherited success/refinement theorems, a 32-byte positional-rank closed form and eight small Nat divisions. These are cohort-model results, not a new source-refinement proof.

The raw twelve-leaf release-kit Funs is instead:

`evidence/extraction-assoc2-20261027/XRj_L013/sources/XRj_generated/XRh_Release/Funs.lean`

SHA256 `f4b2d17c061ce7062d64146531788b6448328e656fb6dbd6192f2d61db31a3b5`. XRh_PINNED-RESULT expressly says emission alone establishes neither elaboration nor adoption. The retained XRj_L013 log reports incompatible mutable Iterator/FnMut and from_fn Result signatures (especially lines 3693, 3705, 3766). There is no admitted unadapted executable environment in which to assert four raw Results. No raw file was repaired or compiled with an axiom template in this job.

For the **XRn kit**, `SDX_kit_manifest.json` pins all 17 original files and the solely name/import replacement `XRn_Join → SDX_Join`. Inverting that replacement reproduces the originals exactly. All were rebuilt privately against SInt2. `SDX_PResult.emitted`, `SDX_ZeroResult.emitted`, `SDX_P1Result.emitted`, `SDX_FFResult.emitted` prove:

| Block | XRn complete Result | Receipt |
|---|---|---|
| P | ok([0,0,0,0,0,0,0,0],2147483647) | L023 |
| zero | ok([0,0,0,0,0,0,0,0],0) | L025 |
| P+1 | ok([1,1,1,1,1,1,1,1],2147483648) | L027 |
| 32 ff | ok([255,255,255,255,255,255,255,255],4294967295) | L029 |

Each uses eight separately proved emitted loop steps, a finite loop composition, eight separately proved byte-word reads and a symbolic constant-callback traversal. No whole sampler recurrence was normalized. L033 audits the eight complete Result theorems and the P disagreement. All accepted prints contain only propext, Classical.choice, Quot.sound (or a subset).

## Q3 Location
The XRn loop discards division at Funs:3623. Raw emission and external restoration must be distinguished.

## Q4 Scope
Pending full emitted call-site inventory.
