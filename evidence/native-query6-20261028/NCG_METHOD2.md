# Function-contract shape fidelity

Pending full controls. Every row is provisional until its positive and matched negative results are checked. Kani0.67.0/CBMC6.8.0, fixed offline frozen graph and lock, KMX patch exact upstream.

Initial Result<u32,Error>:
- K010 identity proof_for_contract PASS; K011 inverted ensures FAIL.
- K012 weak contract PASS; K013 real caller PASS.
- K014 weak stub_verified caller COMPILE FAILURE: Error lacks Arbitrary. This is not the required logical FAIL.
- K015 undeclared modifies write FAIL.
- K016/K017 verified call-site installation/control COMPILE FAILURE for same missing trait.

No Result contract reliance is admitted from these initial runs. Repair only in own scratch harness: exhaustive generator for all eight frozen/default-feature Error variants. No variant/return is assumed successful. Option<M31> needs a field-crate cfg(kani)-only harness implementation of Arbitrary for public M31(u32), with all u32 values (no canonicality restriction). Slice-reference and Result<Vec<u64>,Error> shapes receive their own controls. These tests do not themselves establish a decoder, allocator, or complete caller bridge.

Option<M31> controls are complete: K022/K023 identity/inverted ensures; K024 weak callee; K025 real caller; K026 uninferred caller assertion under verified stub FAILS; K027 modifies violation FAILS; K028/K029 exact installed identity PASS/FAIL. The scratch-only field-crate Arbitrary instance spans ALL U32 values, including noncanonical ones. No function pointers occur.

Slice controls: K030/K031 contract/inverted ensures PASS/FAIL; K032/K033 weak/real PASS; K034 `stub_verified` COMPILE FAILURE (`&[u32]` lacks Arbitrary); K035 modifies violation FAILS. K036/K037 were skipped because the same representability blocker prevents reliance. Do not infer slice-reference, actual geometry, or ownership installation from the passing callee tests.

Own transport wrapper was tightened to serialize all SSH, including read-only snapshots. It changes no proof assertion/admission/runner. Own queues now halt on compilation or timeout before repeating a blocked shape; missing attempt numbers mean no launch.

Allocator Result<Vec<[u64;4]>,Error>: K038/K039 contract/inverted ensures PASS/FAIL; K040/K041 weak/real PASS; K042 verified weak substitution COMPILE FAILURE (exact Result<Vec<...>,Error> lacks Arbitrary); K043 modifies violation FAILS. K044/K045 and the downstream allocator contract queue are not admitted. No synthetic carrier or unsafe Vec construction is substituted. Full allocation/view/ownership remains open.

K046 failed compilation before the intended Result control: the unselected actual-decoder caller annotations already required a contract on M31::from_le_bytes. Own input repair installs the cfg(kani)-only contract before compiling the module, with the frozen decoder body unchanged. K046 gets no semantic credit. Later attempts use fresh IDs and snapshot exact direct/inverted annotations.
