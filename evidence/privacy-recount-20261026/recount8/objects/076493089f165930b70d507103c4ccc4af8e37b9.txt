# Next consumer of the pinned weight closure

The actual current `prepare_opening` calls op252 once, then op253 for the
inactive scalar, and op251 for materialization on that same returned object.
`PV_B2_F_RawNative` supplies the installed complete-Result associations through
`ResourceFamilies`, including Box/heap failures and divergence. Its state is
`PV_B2_F_MaterializeNative.W` (`ExternalTypes.op25`), not an arbitrary replacement
state. The next new theorem must map that exact object's variant, five matrices,
three points and two extra values to `ProverCommitWeightsStorage53.State`, then
prove that its raw rows agree with `weights53.row` and its materialization agrees
with `ProverCommitWeightsMaterialBinding53.run`. It must bind the constructor
itself to `weights53.new`, without assuming the desired state or raw table.

The consuming opening theorem is the actual `prepare_opening` / `finish_opening`
Result association with `ProverCommitOpeningModel53.exact_result`. That theorem
must retain transcript calls and both Result layers; the retained arithmetic
kernel is not a substitute for these constructors. No native effect or endpoint
credit follows from loading the weight prerequisites.
