# R201 complete current serializer execution

R201 proves the actual selected current `bytes_loop` and `bytes` declarations equal the completed wrapping serializer after a limb-preserving type conversion. These result/error/divergence equalities hold for arbitrary iterator state and buffer, and arbitrary input slice respectively, without size or canonicality premises. Under the explicit output-size bound, the serializer succeeds with the exact little-endian bytes already proved generically. The new body and decreasing-rank lemmas discharge both premises of the finite-loop helper.

The focused target compiled in the pinned capped Lean 4.32 cache: exit 0, 1.03 seconds, peak RSS 2,547,176 KiB, zero swaps. All three complete axiom reports contain only the standard foundations. The [evidence](evidence/r201-current-bytes-execution/manifest.json) records the exact compile revision, source checksum, command, complete log and harmless warning. No completed generic serializer check was rerun.

Next: prove selected vector header/payload `Vec::extend` and the captured-borrow gamma slice fold, then bind the complete actual freeze and callback/oracle chronology through rho. This serializer result proves neither a whole callback trace nor a challenge law, privacy or soundness. Verifier source, genuine CU results and all security parameters remain unchanged.
