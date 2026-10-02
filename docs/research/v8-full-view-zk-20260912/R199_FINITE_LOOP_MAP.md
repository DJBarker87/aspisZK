# R199 finite loop state-map helper

R199 proves that two finite Aeneas loops return the same result when their one-step executions match through a state map and every successful continuation decreases a natural rank. Both premises must be proved for each concrete application. The helper preserves body failure and divergence.

The focused target compiled in the pinned capped Lean 4.32 cache: exit 0, 1.01 seconds, peak RSS 2,530,480 KiB, zero swaps. Its complete axiom report contains only the standard foundations. The [evidence](evidence/r199-finite-loop-map/manifest.json) retains exact source, launcher, log and the harmless unused-simp warnings.

Next: prove the current byte-loop’s mapped body equality and decreasing rank, then apply this helper to reuse the completed generic serialization theorem. This generic lemma alone proves no source byte-loop, whole callback, trace, privacy or soundness claim. No verifier source, benchmark or unchanged regression changed.
