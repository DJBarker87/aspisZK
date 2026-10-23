# Actual native Pair acceptance reaches its same tensors

`AspisR1S9ActualPairTensorCallsV1.actual_pair_success_tensor_calls` starts with only the SAME accepted actual native `Weights.pair` call, the admitted S2 variant and two-fold alpha length. The existing allocator interface remains explicitly quantified. No canonicality, process-kind success, tensor success or generic helper contract is supplied as a premise.

It derives the actual f-length division/n, expected-size loop and passed size guard; both actual alpha reads/powers producers; the actually allocated scratch; the actual shared-two-point guard; and the regular-kind source trace on the ORIGINAL receiver with actual f/n/powers and initial zero parts. This processing is before pair_loop1, so no later self1 receiver is substituted.

Each trace entry retains both the SAME process_kind success and its SAME internal tensor success on that entry's actual mutable scratch-borrow slice. Real intermediate scratch and parts states are chained in execution order.

The branch sets are exact:

- Shared: kinds2,5,6 invoke tensor rows1,3,4.
- Unshared: kinds1,2,3,5,6 invoke rows0,1,2,3,4.

No tensor call for kinds1/3 is invented in the shared branch. The S2 equality DERIVES exclusion of the D dense branch. Concrete source kind-to-row mappings are proved using the existing bounded wrapping-subtraction theorem; machine moduli are not unfolded.

Four focused source results compose: process-kind tensor reachability; exact three/five-call regular trace; accepted Pair prefix; complete accepted Pair-to-tensor trace. Existing actual-source Try/Result inversion patterns and bounded arithmetic were reused. The final theorem supplies the previously explicit internal tensor-success witnesses for later native tensor mathematics; it does not itself prove all Pair arithmetic/output semantics or shared-high/inactive/libra behavior.

Validation: 12.784s,12.799s,10.204s,9.840s; standard-only axiom reports; zero swap; under8GiB. Rejected reduction/Try-boundary/typed-division attempts are retained. Initial final-target workspace was admission-only due to a legitimate foreign mutex holder; no compiler was launched until release. No lock was stolen and no parallel local compiler ran. Exact current qualified source hash is371afe30…; source/import/profile/toolchain pins are included. No binaries or cold dependency builds are included.

Complete sourcecut/allocator/Rust/Box/runtime/caller/artifact correspondence, whole Pair semantics, full S9, privacy and composed100-bit soundness remain outside this reachability closure.
