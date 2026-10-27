# Native expansion canonicality and symbolic split values

018 FJa_ExpandCanonical.loop: complete installed coordinate loop preserves
canonicality on its SAME actual slice, by induction on remaining coordinates.
019 FJa_Expansion.canonical_result: original expand seed/update/iterator
constructor supplies the initial canonical array; no seed premise.
025 FJa_SplitValue.writes: exact values of original two writes on SAME operands.
027 FJa_SplitFold.value: complete native descending loop equals symbolic
fold of those literal writes. 022/023 check symbolic outside/children shape;
028 checks exact doubled-width total mass conservation for that fold.
No deployed premise removed, no boxed mass or literal point result yet.
Standard axioms only on each checked theorem; receipts pin all source/deps,
commands, revision/dirty hashes, exit, wall, peakRSS and swap0.
All runs capped at 6G/8G/swap0/tasks64, -M7000. No timeout/memory kill.
024 failed on simp_all eq_comm recursion in a tiny update adapter, corrected
by splitting address conditions (025), without raising any limit.
