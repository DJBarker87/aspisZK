# Complete typed preparation value and ordered hash replay

NBL_QueryEffectFactor.source (L064) factors the EXISTING eager query effect
tree. NBL_QueryQuietFinish.source (L065) proves its entire decode/embed suffix
has no digest events for all Results, without presupposing decode success.
NBL_MaterialHashReplay.source (L068) links the sixteen chronological read/
advance attempts to the SAME blocks/advances. NBL_QueryHashReplay.source
(L070) includes the absorb attempt and retains all seventeen events on every
decoder Result, including rejection and earlier-state selection.

L062/L066 hit the existing recursion limit during whole-expression simp.
They were replaced by binder-local factoring and NBL_RunStep chronological
steps; limits/caps unchanged. L069 normalized afterAbsorb too early to use a
local equality; L070 normalizes that equality too. Failed prints excluded.

NBL_ContinuationHash (L072) handles exact query error + old scratch, both claim
Results + produced scratch, and composition after opening. L071 needed the
explicit FromSame.from reduction and normalization of emptyPayload.
NBL_PrepareHashTrace.source (L075) constructs native powers/claim and proves
the FULL EXISTING cohort effect-code result: Prepared, final scratch and all33
chronological digest attempts, from one linked opening/query/rho trace and
the SAME model producing executions. It uses the caller-domain derivation,
not a whole prepare equality premise. L073 fixed a namespace; L074 explicitly
normalizes the local dictionary/output projections. Standard axioms only.
NBL_PrepareHashReject.source (L076) proves the exact30-attempt rejection prefix
and old scratch, with no fabricated rho/powers/claim suffix.

This closes the previously missing cohort ordered-effect replay, NOT the
native execution instance. OPEN native producer/trace associations remain;
no CLOSED composite credit, headline premise removal or changed trust item.
