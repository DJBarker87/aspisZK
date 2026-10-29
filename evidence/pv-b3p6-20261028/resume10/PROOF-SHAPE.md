# Value-entry proof shape history

64000 passed a shallow tail14 law, but the first generator's extraction span
also included three irrelevant subsequent declarations; those are not binding
credit. 64001 rejected duplicate declarations plus an opaque-tail rfl failure.
The span was trimmed to the next doc comment (295 body lines, not409).
64002–64007 passed smaller tail equations. 64008 rejected because simp visited
the large source tail. Restricting simp to the stage RHS changed the shape;
64009–64016 passed, but64017 rejected at final raw-tail rfl.
Direct scalar live-in parameters removed repeated tuple projections:
64018–64025 passed;64026 still rejected at raw-tail rfl.
No limit was raised. The rejected raw-tail family is superseded by shallow CPS
head equations: the remaining tail is a universally quantified function,
never a duplicated large expression to compare. 64027 had redundant trailing
rfl commands after simp had already closed two small goals; removing them
produced64028's accepted selector/head laws. No theorem from64027 is credited.

The root will rewrite one named head, descend through bind congruence, and
repeat; this is the D411 digest direction. Only successful current source
snapshots will enter the three audits. The source-entry law alone does not
supply exhaustive shipped-to-owned structural binding.

64042 rejected the root's whole-body unfold, before any head composition.
64043 avoided the unfold and consumed the complete first head, then exposed
that rewriting could not infer a continuation through tuple projection.
Named scalar/range continuations and explicit continuation arguments fixed it.
64044 reached all proofs with accepted axioms but a redundant trailing rfl
made the file fail;64045 passed the actual CPS entry/read law.
64047 passed all thirteen selector frame laws.64048/64049 retained a final
opaque-continuation/reflexivity error in the existing-sequence join;64050
passed value_entry_factor10 and add_value_read_binding10. No large source
body is unfolded in that accepted entry proof, and no limit was changed.

64061 accepted the complete emitted accumulator storage binding (all96
storage/pure steps, with the four field Results unchanged), after named pair
and pure-let head elimination exposed each delayed restoration.64062 accepted
its composition with all nine named cell Result laws. These are model/storage
laws, not a native differential and not the complete terminal source binding.
