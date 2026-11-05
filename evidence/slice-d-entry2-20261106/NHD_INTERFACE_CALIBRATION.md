# Exact-signature controls required by the NGL finding

**BLOCKED: all three required stub_verified semantic controls are unexecutable. Zero admitted rows.** Nominal receiver, arguments and returned lifetime are preserved in these pilots; the weak contract intentionally omits the caller assertion. The readonly real-body pilots execute the frozen helpers. The borrowed pilot projects the same actual Vec place from a valid OwnedAccount receiver. Its four-byte healthy allocation is only a type/provenance control, not a deployment-capacity bridge. Modifies mutants add one explicit local mutable byte observer to the otherwise matching signature; this extension is recorded, not silently generalized.

| NGL signature | Real body PASS | stub_verified result | Modifies FAIL | Retained inverted control |
|---|---|---|---|---|
| metadata, five arguments -> ProgramResult | K049 | K050: Arbitrary compile rejection | K051: assignability check | NGL_K038 |
| OwnedAccount + owner -> ProgramResult | K052 | K053: Arbitrary compile rejection | K054: assignability check | NGL_K107 |
| borrowed OwnedAccount -> borrowed-slice Result | K055: SAME pointer/length | K056: Arbitrary compile rejection | K057: assignability check | NGL_K065/071/077/091..105 |

Full signatures, harnesses and receipt links are in NHD_CALIBRATION.json; each K identifier denotes NHD_Kxxx/receipt.json. Declared weak-contract proof harnesses exist for compilation, but were not independently run or claimed verified. There is no reliance on those declarations as callee proofs. The required failing caller assertion cannot be executed. No Bool subset, carrier mirror, orphan trait implementation or patched SDK dependency is substituted for it.

# Auxiliary carrier probes and configuration

**BLOCKED. No adapter certificate is admitted.** A compile error is not a failing semantic control. All three `stub_verified` callers fail to compile because the foreign `ProgramError` result does not implement `kani::Arbitrary`. We do not replace the SDK error type, add an orphan implementation, weaken the contract-interface rule or treat this as an implementation counterexample.

The result-carrier pilot below additionally probes Result<usize,ProgramError>. The exact three signatures enumerated by NGL_FIDELITY_FINDING are tested separately in the primary matrix. The duplicated borrowed-result wording in the job is not used to infer coverage.

| Interface | Harness | Verdict | Receipt |
|---|---|---|---|
| ProgramResult | program_contract | PASS, pilot weak contract only | NHD_K002/receipt.json |
| ProgramResult | program_real | PASS, real body implies caller assertion | NHD_K003/receipt.json |
| ProgramResult | program_stub | COMPILE ERROR; required FAIL unavailable | NHD_K004/receipt.json |
| ProgramResult | program_modifies | FAIL, out-of-frame write detected | NHD_K005/receipt.json |
| Result<usize,ProgramError> | length_contract | PASS, pilot weak contract only | NHD_K006/receipt.json |
| Result<usize,ProgramError> | length_real | PASS | NHD_K007/receipt.json |
| Result<usize,ProgramError> | length_stub | COMPILE ERROR; required FAIL unavailable | NHD_K008/receipt.json |
| Result<usize,ProgramError> | length_modifies | FAIL, out-of-frame write detected | NHD_K009/receipt.json |
| Result<&[u8],ProgramError> | slice_contract | PASS, pilot weak contract only | NHD_K010/receipt.json |
| Result<&[u8],ProgramError> | slice_real | PASS, SAME pointer and length | NHD_K011/receipt.json |
| Result<&[u8],ProgramError> | slice_stub | COMPILE ERROR; required FAIL unavailable | NHD_K012/receipt.json |
| Result<&[u8],ProgramError> | slice_modifies | FAIL, out-of-frame write detected | NHD_K013/receipt.json |

Harnesses are under `NHD_calibration::`. Every mutable frame observer is a local u8 passed by mutable reference; no writable static, function-pointer observer, cast guard or byte-havoc provenance claim is used. The real-body and stub callers have identical assertions; the weak pilot postcondition intentionally does not imply them. The frame mutants write outside an empty modifies set. The three semantic frame failures each report one failed assignability check. They are distinct from the three compiler rejections.

Exact association, had the gate passed: ProgramResult is the result family of readonly_meta_ok, require_readonly_account and require_verifier_checkpoint; Result<usize,ProgramError> is OwnedAccount::data_len; the lifetime-preserving borrowed slice result is OwnedAccount::data. These pilots do not calibrate their argument structures, arbitrary allocation capacities, foreign Ref guards, authentication output structures or enclosing effects. No calibration is claimed complete.

NGL inverted controls are retained by SHA256 in NHD_REUSE.json: K038 (metadata), K107 (owned readonly), K065/K071/K077/K091..K105 (data). NGL native/model evidence is reused read-only. Its source, original harness names and prior timeout verdicts are preserved. The new pilots are calibration functions, not renamed retries of NGL failures.

All native runs use the pinned Kani 0.67.0 toolchain, deployed pool-adapter/private-leaf-salts, optimized offline compilation and a pre-run frozen dependency-graph check. Every completed run records the unchanged frozen lock after Kani. The scratch tree retains the exact KMX patch bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67; its three component hashes are asserted in NHD_gate.py. No pilot asserts a buffer-copy law or claims a new copy pass. Existing copy-dependent helper passes remain conditional on their original matching NGL KMX controls, as indexed in NGL_NATIVE_REVIEW.json.

K001 is an excluded input compile error: the new module omitted `extern crate alloc` needed by the unchanged included KMX source. K002 adds that import and passes; no timeout or memory kill was retried. Both input versions and receipts are retained. All runs have fresh admission (exit 0 and allowed:true) and the required 6G/8G/swap0/tasks64 scope. Full commands, frozen revision, source/dependency hashes, elapsed time, peak RSS, swap and N/A Kani axioms are in each receipt.

Auxiliary weak-contract inversion controls also fail semantically as intended: K058 for K002, K059 for K006, K060 for K010. They check deliberately inverted ensures on identical result carriers and scalar/slice argument shapes; no contract baseline is left supported only by a modifies mutant. The actual helper inverted controls remain the retained NGL runs above.
