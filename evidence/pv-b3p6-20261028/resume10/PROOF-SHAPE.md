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
