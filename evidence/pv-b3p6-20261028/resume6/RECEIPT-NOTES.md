# Receipt notes

100 charged Lean attempts;81 passing targets,19 rejected attempts; four
uncharged reservation refusals. Each refused ID was retried only after its full
180-second cooldown, with the same ID. Pre-cooldown guard checks launched no
scope and spent no attempt. The runner's exhausted regular-range sentinel
`next_unused_id=60897` is NOT an unused ID: all60800–60899 are spent, including
the three audit IDs. The100-attempt guard prevents any further launch.

Every source snapshot matches its submission hash. All81 latest accepted
module sources match the current files. A failed compiler invocation may print
`sorryAx` while recovering from an error; those invocations receive no credit.
The final97-theorem audit accepts only propext, Classical.choice and Quot.sound.
No checked ledger-row/endpoint counterexample was found.

The wrapper's original #print-axioms regex captured only one continuation line.
The committed JSON receipts/index now contain the complete multiline blocks
parsed from the UNCHANGED stdout/stderr logs. No proof was rerun for this
metadata correction. Exact commands, revisions, status/resource measurements,
source snapshots and dependency fingerprints remain unchanged.

The global-sum failures60862 and60870 were recursion-depth elaboration failures,
not memory kills. After isolation,60884 proves the same actual emitted helper
by shallow named success-rule applications, without unfolding the entire body
or raising maxRecDepth/maxHeartbeats. Pure lifted index expressions are retained
with the named lift_bind law; bounds on RATE and the source layout constants
are supplied symbolically. No whole reference or installed-callback success
is inferred from these helper results.

The resume5 cache had been removed. The first44 focused dependencies were
recompiled because their object artifacts were missing; no unchanged complete
privacy regression was run. This round reused its pinned private workspace and
objects throughout all dependent targets, then removed only its81 private proof
objects under local-lean rule9. Source, receipts, object hashes and LLBC remain;
no keys, shared sources, crates, programs, simulator or observer were changed.

## Rejected attempts (all retained)

|ID|Module|First error|
|---|---|---|
|60845|PV_B3P_Success227|`dsimp` made no progress|
|60851|PV_B3P_DotSuccess227|`dsimp` made no progress|
|60854|PV_B3P_ReverseSuccess227|omega could not prove the goal:|
|60856|PV_B3P_ExpandInnerSuccess227|omega could not prove the goal:|
|60857|PV_B3P_ReverseSuccess227|unsolved goals|
|60858|PV_B3P_ExpandInnerSuccess227|unsolved goals|
|60861|PV_B3P_ExpandSuccess227|Type mismatch: After simplification, term|
|60862|PV_B3P_PoseidonBaseSuccess227|maximum recursion depth has been reached|
|60864|PV_B3P_PackLoopSuccess227|Unknown identifier `reference_field.qm31_pack_base4_loop`|
|60865|PV_B3P_ClaimSuccess227|Tactic `rfl` failed: The left-hand side|
|60869|PV_B3P_ClaimSuccess227|Application type mismatch: The argument|
|60870|PV_B3P_PoseidonBaseSuccess227|maximum recursion depth has been reached|
|60874|PV_B3P_SemanticBasicsSuccess227|Tactic `apply` failed: could not unify the conclusion of `@bind`|
|60876|PV_B3P_ArraySelfSuccess227|failed to synthesize instance of type class|
|60878|PV_B3P_AbsorptionSuccess227|scalar_tac failed to prove the goal below.|
|60879|PV_B3P_ArraySelfSuccess227|Tactic `rewrite` failed: Did not find an occurrence of the pattern|
|60881|PV_B3P_AbsorptionSuccess227|scalar_tac failed to prove the goal below.|
|60889|PV_B3P_PublicSuccess227|unexpected identifier; expected '}'|
|60890|PV_B3P_PublicSuccess227|unexpected identifier; expected '}'|
