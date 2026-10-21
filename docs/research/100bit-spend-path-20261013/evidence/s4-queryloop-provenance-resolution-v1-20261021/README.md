# Stage2ContinuationQueryLoop owner provenance resolution

The earlier query-equality packet compared its selected object against the v1 producer receipt by mistake. The exact selected object SHA is `20a8d68464f20012572d37f1228045ac2a42a5776e3d5f8281f7180b24c0d450`, which matches the successful v2 receipt. That receipt records source SHA `c398ba41273939ac739a064eee492976988027ff1b1d6f33657480b17aed0def`, matching the current tracked source snapshot. Thus the owner object used in the equality proof has current-source provenance.

The archived v1 source has a single proof-only diff: private `actual_body` used `simp only [verifier.candidate.query_loop_loop.body, Stage2ContinuationOwnedLoop.body, UScalar.ge_equiv]`; current source uses `rfl`. The query-loop and body definitions themselves are unchanged. No source-generation adapter is involved. The exact diff and both source snapshots are retained here.

This is a provenance correction only; no Lean replay was necessary. The v2 producer receipt records exit 0, Lean 4.32 compiler SHA, peak RSS and zero swaps.
