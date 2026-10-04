# R688 combine-beta field interpretation

R688 interprets the actual successful selected `combine_beta` output as a QM31 expression over `M31Exact = ZMod P`. Under the same successful `r55_decode_into` equations and canonical coefficient-word bounds used by R687, it produces the selected four-slot lane array, retains all 16 canonical-limb bounds, and proves each decoded four-word output equals the sum of 26 C1 scalar-word times QM31 coefficient vectors plus three defined 4×4 mixed-matrix actions on the corresponding C2 words.

The proof uses R687’s exact 38-term modular output equation, casts it into `ZMod P`, groups the twelve C2 terms by the `Fin 3 × Fin 4` equivalence, and projects the defined QM31 expression coordinate by coordinate. It makes no premise that the beta-coefficient constructor produced these arrays, no field-multiplication claim for the matrices, and no claim about the original quotient pair, callback, oracle, privacy, or soundness.

Final focused target: `AspisV8R19/R688CombineBetaFieldInterpretation.lean`; run `1791122891583439000`; exit 0; wall 2.72 s; peak Lean-child RSS 3,789,820 KiB; swap 0. Source revision `30b4e1b4c3ec550cb7530641d8367e8d64ad65b8`; source SHA-256 `6cd61514daf20322e76aebd7b72ea7a2224e76ce8d79e81e0ebb16fb3f95e5c6`. The run used the pinned Lean 4.32 cache with `-j1 -M4500`, `MemoryHigh=5G`, `MemoryMax=7G`, `MemorySwapMax=0`, and `TasksMax=128`.

The complete final axiom report is `[propext, Classical.choice, Quot.sound, core.fmt.Formatter]`. `Formatter` is inherited from R687’s successful decoder/wrapper route. R688 adds no `sorryAx` and does not establish native adequacy of that generated route.

The first failed attempt, `1791121871180874000`, is preserved because it records the direct R620 import collision between incompatible R618 and R614 generated type modules. R688 copies only R620’s mathematical matrix-coordinate/action definitions into the R614 type environment; the provenance and precise limitation are recorded in [IMPORTS_AND_PROVENANCE.md](evidence/r688-combine-beta-field-interpretation/IMPORTS_AND_PROVENANCE.md). All changed failed and superseded focused attempts are retained in [ATTEMPTS.md](evidence/r688-combine-beta-field-interpretation/ATTEMPTS.md).

The next missing proof is the actual field meaning of the coefficient arrays and their relation to the original quotient pair and full callback. This result alone does not establish end-to-end privacy or security.
