# Prover commitment continuation 5 — 2026-10-21

Branch `codex/cx-prover-commit5-20261021`, base `a7b7621d9`.
Evidence: `docs/research/100bit-spend-path-20261013/evidence/prover-commit5-20261021/`.

## Stage 1: single-try verification and symbolic composition

The two timed-out full 16-try harnesses are not rerun. New proof-only
`mask_try_step` and `source_try_step` harnesses compare one carried-result
transition on arbitrary valid state (word slot 0 through 8, arbitrary seed,
counter and cached block). Success is absorbing; failure consumes exactly
one shipped `next_word` and classifies the candidate with the shipped try
expression. Both sides use the same retained memoised oracle, including
repeat lookups and possible collisions. The capacity/call budget is asserted
at two, not assumed. The post-state comparison includes every expander
field and the valid-slot invariant. `check-step-source.py` pins and checks
both source try bodies, their 16 limit and the normalization used by the
harness. The actual production sampler bodies are unchanged.

`ProverCommitSamplerComposition` proves early-return/carried-loop equality,
success absorption, and invariant-restricted composition for any loop length,
including 16. Env J 8158 passes, 1.49 seconds, 2,578,208 KiB peak RSS, zero
swaps. Its four theorems use no axioms. The local equality is a named
hypothesis: a Kani receipt is not silently installed as a Lean axiom.

Further stage receipts and the exact source frontier follow below.

## Stage 2: checked H1 quotient and completion

`ProverCommitTapeCompletion` splits the **actual** `Tape K F` into a
`SourceTape` quotient and `Padding`. Ignored coordinates are precisely H1
lane 1 at row 0 or a copy-active row. All other affine coordinates and all
eligible noise remain in the quotient. `completionEquiv` is a lossless
bijection `(SourceTape × Padding) ≃ Tape`; every full tape has one fibre.
`quotientFibreEquiv` identifies every quotient fibre with the same `Padding`
type. These are symbolic bijections; no tape enumeration or huge finite
reduction occurs. The dependent-row balance lemma handles the erased row
symbolically, and `h1_completion` proves padding choices cannot change H1.

`ProverCommitTapeMeasure` proves uniform product completion is uniform on
full tapes, uniform full-tape projection is uniform on the quotient, and
**any observable factoring through the quotient** has the same law under
an arbitrary representative (including zero fill). `applyAff_completion`
checks the entire affine trace operation, including ordinary mask columns,
G, H1 and D, against the actual definitions. This avoids claiming a
zero-filled *raw tape* is uniform. It proves uniformity only of the
observable that ignores the redundant coordinates.

Accepted attempts: 8162 (completion, exit 0, 1.89 seconds, 3,531,948 KiB,
zero swaps) and 8164 (measure/trace, exit 0, 2.09 seconds, 3,526,584 KiB,
zero swaps). All thirteen theorem audits use only `propext`,
`Classical.choice`, `Quot.sound`. Rejected drafts 8159–8161 and 8163 are
retained and excluded. Source SHA/dependency fingerprints and full outputs
are in `lean/`. The launcher snapshots this job's previous versions before
replacing its own shared objects; no peer-owned module is replaced.

This construction makes completion randomness explicit. It does not prove
that the shipped expander streams provide independent uniform `Padding`,
or identify a source decoder with a uniform quotient law. A quotient
privacy endpoint must transport every relevant observable, not merely
`applyAff`. Thus this stage does not install `R_commit_equal_fibres` for an
existing `Pr`, assume a cF, or silently change the existing protocol endpoint.


## Stage 3: extracted-loop and endpoint joins

Both single-try harnesses pass, with explicit unwind 514 and enabled
unwinding assertions: mask exit 0, 29.413 s, 607,924 KiB, zero swaps;
source exit 0, 30.460 s, 632,236 KiB, zero swaps. Each asserts the 2-call
budget and retained-cache capacity. No oracle reset occurs between sides.
The accepted structured outputs report 0 failed properties. Kani axioms:
N/A. Receipts retain exact commands, cgroup limits, source hashes and revision.
The old 16-try SAT instances are never run.

`ProverCommitExtractedStep.extracted_body` factors the **existing Aeneas
reference loop body** into its single carried transition, retaining all
`Result.fail`/`div` behavior. `ProverCommitExtractedLoop.reference_limb_sixteen`
proves the actual extracted sampler equals 16 Kleisli compositions of that
step. The proof inducts on remaining tries and proves the I32 increment
cannot wrap in the interval 0–15; it never evaluates an oracle answer.
Accepted attempts 8177 and 8183: exit 0, 1.96/1.47 s,
2,581,772/2,592,508 KiB, zero swaps, standard axioms. This supplies the
requested composition argument without unrolling sixteen try bodies in
one SAT instance. The Kani/source syntactic bridge and Lean extraction are
separate evidence: no Kani receipt is promoted to a kernel theorem.

`ProverCommitCompletionAdapter` constructs a partial full-tape decoder from
`Input × Padding`, proves failure iff original failure, and gives an
explicit equivalence between **each** completed successful fibre and the
original quotient fibre. No common fibre constant is assumed in that
cardinality theorem. Attempt 8175: exit 0, 2.27 s, 3,525,728 KiB, zero swaps.
`ProverCommitBudgetJoin` proves capacity plus block upper bound forces
E=2L, count/block premises imply both 64-bit counter bounds, and counters
below that budget cannot wrap. Attempt 8178: exit 0, 1.40 s,
2,384,612 KiB, zero swaps. `ProverCommit5Joins` joins the latter to the
actual endpoint counter slots and joins completion failure to actual
`RExh`/`wordsE`, with the source caller/failure law explicitly required.
Attempt 8181: exit 0, 1.59 s, 3,525,596 KiB, zero swaps.

`ProverCommitQuotientView` transports the complete existing honest joint
view, all payload cells included, from uniform full tapes to uniform
quotient tapes with **any** deterministic padding representative. Attempt
8184: exit 0, 1.58 s, 3,519,548 KiB, zero swaps. This is a checked honest-view
quotient endpoint; it is not yet the retrying ROM protocol source endpoint.

## Demonstrated remaining obstruction

`ProverCommitSectionObstruction` strengthens the previous zero-fill result:
**every deterministic section from quotient tapes alone misses a full tape
and cannot have equal successful fibres over full tapes.** The proof changes
one ignored dependent-row limb, uses the checked projection/completion
inverse laws, and never enumerates a tape. Attempt 8186: exit 0, 1.65 s,
3,524,164 KiB, zero swaps, standard axioms.

Consequently the checked observable quotient theorem cannot simply be
passed into the existing `R_commit_equal_fibres` slot. That slot quantifies
over full raw `Tape K F`, while `completeDecode` takes an explicit extra
`Padding` factor absent from `Pr.tapeOf`'s two byte-stream inputs. No equality
or measure-preserving map from those actual inputs to this enlarged input
has been constructed. The section obstruction does not rule out using
additional randomness already present in the full source inputs.

The existing `R1ProverP` fields `tapeOf`, `leafVal`, `caddr`, `E₁/E₂` and `ord`
are residual data, not an extracted sampler/builder instance. In particular
arbitrary `leafVal`/`caddr` can inspect a raw ignored coordinate; invariance
of the honest view does not prove invariance of those fields. The concrete
caller/packing law, a successful-source quotient fibre law, full commitment
observable invariance, and universal read/count coverage are still needed.
`RExh` requires failure classification for that concrete decoder on exact
`wordsE` inputs; the proved adapter only transports such a law once supplied.
No extra rejection/failure is introduced to sample padding, and no claimed
exhaustion classification is based on decoding unused worst-case words.
The previous checked padded-suffix counterexample still excludes that route.

No builder/SourceIdentification/history file is edited or replaced. Those
concurrent workers' proof boundaries are not assumed solved. No complete
one of the nine checklist rows closes; the two counter **subslots** are now
derivable from existing count/block premises. No unconditional source
privacy claim or assumed cF is installed.

## Final ELF gate and axioms audit

The only Rust changes are cfg(kani) additions. Source `ac2d238e9` is rebuilt
under MemoryHigh=6G, MemoryMax=8G, MemorySwapMax=0, TasksMax=64, four jobs,
Solana 3.1.13/platform-tools v1.52, locked offline dependencies and exact
frozen feature sets. Native RUSTFLAGS is `-C link-arg=-Wl,--threads=4`;
the pinned SBF recipe unsets it and uses the target-specific
`-C link-arg=--threads=4`. Expected work is incremental optimized SBF
compilation/linking, not proof generation. Host reservation waits precede
launch; receipts preserve all populated caps and limits.

| Program | SHA256 | Exit | Wall s | Peak RSS KiB | Swaps |
|---|---|---:|---:|---:|---:|
| default | `dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34` | 0 | 2.490 | 203476 | 0 |
| devnet | `fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78` | 0 | 2.431 | 203464 | 0 |
| pool | `121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548` | 0 | 0.416 | 99580 | 0 |

All three pass cmp against the retained frozen artifacts. No runtime or
adversarial suite is repeated: shipped bodies and frozen ELFs are unchanged.
No key is deleted or read; generated key files stay retained at mode 0600.
No deployment, transactions or push occur. Build axioms: N/A.

Final coherent new-cone audit `R1Z.ProverCommit5Audit`, env J **8187**:
exit **0**, **1.77 seconds**, **4,042,968 KiB** peak RSS, **zero swaps**.
All 44 full audit results (new theorems/three equivalences and the unchanged
protocol endpoint) are free of `sorryAx` and use only subsets of
`[propext, Classical.choice, Quot.sound]`; the four elementary composition
theorems use no axioms. Exact sources, source revisions, dependency object
fingerprints, outputs, times and rejected drafts are retained in `lean/`.
Attempts 8158–8187 are consumed; next available is **8188**. Failed drafts
are explicitly excluded; no unchanged formal target or full frozen manifest
is replayed. No certificate generation or expensive arithmetic gate runs.

## Before (verbatim):

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_equal_fibres, cF | Exact equal-cardinality successful tape fibres for every τ. Deterministic expansion and successful tests do not establish uniform tapes. |
| R_commit_exhaustion | Every tapeOf failure implies one of the actual two 16-try little-endian stream-exhaustion events; exact source wordsE transport (P`R1Z/FinalR1PBin.lean:44,54`). |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | E≤2^64, 16L≤8E, RCommitCount cell bounds and E≤2L; universal source commitment read completeness. D76's fixture count alone is not this universal refinement. |
```

## After (verbatim; all nine complete rows retained open):

```text
| R_commit_D80.roots/nodes | AddressAt for all three roots/internal binary parents, child order, padded folded geometry, byte carrier and D81 grammar. Do not substitute eight-way C2 recovery for binary recovery. |
| R_commit_D80.leaves | Exact 0x71/0xf1/0x72 tags, packed leafVal/trailing salt, private-leaf backend and byte/digest conversions, on the actual prover tree. |
| R_commit_D80.bindings | Both secret-attempt binding reads, source/public/variant mapping, context encoding and digest answers (P`R1Z/LayoutR1PBin.lean:133`). |
| R_commit_D80.seeds | All three seed derivations, reserved secret distribution and source/D stream selection (P`R1Z/LayoutR1PBin.lean:136`). |
| R_commit_D80.salts | Full per-leaf secret salt derivation, nonce/tree/secret binding and LE32(u) (P`R1Z/LayoutR1PBin.lean:140`); verifier facts only consume disclosed salts. |
| R_commit_D80.mask_expander/source_expander | Stream/domain/seed/LE64(counter), eight words per block, no counter reuse, index/stream selection and complete hash-read coverage (P`R1Z/LayoutR1PBin.lean:131`). |
| R_commit_equal_fibres, cF | Exact equal-cardinality successful tape fibres for every τ. Deterministic expansion and successful tests do not establish uniform tapes. |
| R_commit_exhaustion | Every tapeOf failure implies one of the actual two 16-try little-endian stream-exhaustion events; exact source wordsE transport (P`R1Z/FinalR1PBin.lean:44,54`). |
| R_commit_counter₁/₂, R_commit_stream₁/₂, R_commit_cell_count, R_commit_blocks₁/₂ | E≤2^64, 16L≤8E, RCommitCount cell bounds and E≤2L; universal source commitment read completeness. D76's fixture count alone is not this universal refinement. |
```
