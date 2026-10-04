# R614-E generated `combine_beta` support

This milestone records the exact generated Types and Funs emitted from frozen R604 LLBC by private Aeneas candidate E. Types, Funs, and the complete axioms target all compiled on the pinned Lean cache. This is generated-source compilation evidence; it is not an execution theorem or arithmetic proof of `combine_beta`.

The frozen input is `/home/dombarker/project-offloads/aspis-r604-combine-beta-generic-20261004-b/R604CombineBetaGeneric.llbc`, SHA-256 `5391af65767eee12ff76fbddbe2be730f4cad8af24d526f6030140539fc4ec44`. The local scratch capture is `.r21-scratch/r596-combine-beta-capture/R604CombineBetaGeneric.llbc` (not tracked by Git); the evidence package includes an exact byte-for-byte copy at `evidence/r614-selected-combine-beta/source-input/R604CombineBetaGeneric.llbc`.

The formal targets were:

- `AspisR614SelectedCombineBeta/Types.lean`: run `1791100597473614000`, exit 0, wall 1.11 s, peak RSS 2,574,700 KiB, swap 0. Source revision `96932fbf5fa6bed714933e0d70faf911f8837140`, SHA `ea29065a1fb8756d19fa3a828029f8c9a65e576d2cff375ce5457fa65d1ad336`.
- `AspisR614SelectedCombineBeta/Funs.lean`: run `1791103675091011000`, exit 0, wall 6.29 s, peak RSS 3,265,700 KiB, swap 0. Source revision `5a0c4866840cea2335e7223f15572c4d0e73c0a9`, SHA `0a6f49d0e1fae26a17b68871c2c5914d763e71cea3fa2095a6fe13d5d02520c7`.
- `AspisR614SelectedCombineBeta/Axioms.lean`: run `1791103686617646000`, exit 0, wall 1.05 s, peak RSS 2,550,420 KiB, swap 0. It printed all 92 named declarations; the full unabridged output is in `complete-axiom-report.txt`.

Except for `CM31.new` (no axioms), the generated declarations use `propext`, `Classical.choice`, and `Quot.sound`. Seven declarations also inherit the opaque type `Aeneas.Std.core.fmt.Formatter`: the generated decode closure call, decode loop body and loop declarations, and `combine_beta_loop.body`, `combine_beta_loop`, and `combine_beta`. The dependency is on a type constant whose declaration is `axiom core.fmt.Formatter : Type` in the pinned Aeneas formatter support, not on a proposition about the verifier. The axiom provenance source is preserved in `source-pins/Formatter_axiom_source.lean`.

Canonical Lean files are under `lean/AspisR614SelectedCombineBeta/`. Their bytes match the successful run snapshots. Attempt A through E source patches, candidate manifests, failed build/translation logs, and pre-E/E Lean attempts are preserved under `evidence/r614-selected-combine-beta/attempts/`; compiler executables and generated archives are excluded. The evidence manifest lists and hashes every staged file.

The first remaining proof is execution correspondence for the exact captured 38-term `r83_mixed_limb` body, including `reduce_chunk`, its ten chunk boundaries and wrapping additions, and all captured array-index guards. Proving the resulting constructor is a separate subsequent proposition. No end-to-end verifier, privacy, or security claim follows from this milestone.
