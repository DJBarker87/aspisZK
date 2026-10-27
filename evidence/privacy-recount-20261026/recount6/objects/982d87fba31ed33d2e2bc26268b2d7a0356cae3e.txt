# Installed op84 review (source inspection; import step held)

The installed implementation cannot catch a hash callback error. This statement is a source inspection result pending its pinned installed-instance Lean lemma, not a theorem about arbitrary ExternalFuns.

`PV_CB_Merkle.selected` assigns op84 to `ProverRwSuccessHashes.leaf`; `leaf` is exactly `hash (leafFrame tag values)`. `PV_CB_Op84Exact.op84_source` also equates it to the freshly extracted `PV_CB_ShippedOp84Fresh.aspis_core.r0.merkle.leaf`, whose body calls leaf_with_digest, constructs two slices and directly returns LegacyHashFn.digest, which directly returns `self parts`. No Result recursor catches the callback. There are no input branches in this installed body, so the argument applies to every input, including all admitted inputs, without requiring admission. `PV_CB_CandidateDictionary` and the wire dictionary select this op84 projection. The earlier catch84 countermodel replaces that projection and is not this instance.

The inner hash callback is the callback affected by the earlier interface obstruction. In the source occurrence `ProverRwFull.host_commitment.plain_commitment_leaves_loop.body` (FullFuns line 18921), its error can therefore propagate through the installed op84 leaf. This alone does not compose a complete invocation trace. No exact catching path in the installed instance was found.

Under h4/h4 SCOPE, importing the selected-dictionary cohort is held: `R1Z.PV_CB_Merkle`, `R1Z.ProverRwSuccessHashes`, `R1Z.PV_CB_Op84Exact`, and `R1Z.PV_CB_Op84Funs` have no entry in EJR_final-inventory or the named commit47 freeze. No alternative same-name object is substituted. The lead was asked for the cohort source-freeze authority; independent PV_RE proof work continues.
