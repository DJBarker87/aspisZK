# S1 Claims: checked native row step and extracted owned composition

Whole S1/S6 and the 100-bit target remain open. This packet establishes a
native data/error check at one Claims-loop iteration and an extracted owned
step with a checked Lean composition. It does NOT establish native
initializedness, the allocation/cleanup law or the complete Claims function.
No shipped verifier, protocol, feature or artifact changed.

## Native obligation actually checked

The accepted Kani v6 gate uses the complete actual private ValidatedRecord,
WireError, QM31,29-column rows and Box<MaybeUninit<[[QM31;29];3]>> from a
proof-only isolated frozen crate. The pointer-write expression is the exact
shipped one, including decode_k::<29>(p*29) and its early-return operator.
The actual decoded-array callee is abstracted at its normal-return boundary:
its entire record row/pointer/length and offset are checked, and its return
may be any complete raw29-QM31 row or any default-feature wire error with all
fields. This does not execute/prove the decoder or parser again. The bounded
frame fixture is not a proof for arbitrary parser inputs; outside the abstracted
callee this fragment never reads its bytes. Source/callee transport remains
explicit rather than being inferred from fixture contents.

The harness ranges over every p in0..3,arbitrary full before/decoded words and
all default-feature errors. Only the p preceding rows are initialized. It
checks the same result/error as the owned update and equality of every word
in the initialized prefix. The last successful step consumes the real native
Box via assume_init and checks all three complete rows. The reference does
not replace the real record or Box with an opaque token or narrow field.
Box allocation is harness setup; it is not the shipped heap::uninit helper's
allocation/error/cleanup proof. The reference's complete ghost matrix is not
claimed equal to unread native garbage bytes or allocator state.

v6: exit0,67.303713775s,1,467,384KiB RSS,zero swap,769 checks and3 reachable
covers. The quantity is validation coverage,not a security or closure count.
The scope was MemoryHigh1536MiB,MemoryMax2GiB,MemorySwapMax0,Tasks64. Rust
compilation used -C opt-level=3,-Z mir-opt-level=0,overflow checks and one job.
All six local Cargo source trees and106 compiler/support/native import files
were pinned before/after and unchanged. No native SBF/std identity is inferred.
Native SAT has no Lean #print-axioms result; its tool trust is kept distinct.

## Initializedness audit: not proved

The v6 command has default memory checks,not Kani's separate experimental
uninit-checks instrumentation. After explicitly auditing CLI coverage,we tried
that stronger coverage in v7. It failed before SAT with an internal compiler
error at kani_middle/transform/check_uninit/ty_layout.rs:190:

> FieldsShape::Primitive with a different ABI than ValueAbi::Scalar.

One smaller context v8 retained the same checked fragment,actual complete
wire/token/error/sampler definitions and core QM31 dependency,while omitting
unrelated verifier/statement modules. It failed with the identical ICE before
SAT. Neither attempt is a memory proof or a counterexample to the verifier.
Both source contexts,commands,receipts,tool/import pins and fresh admissions
are retained. No backend was edited,cap raised,or backend campaign started.
A validated initializedness proof/tool route remains required before claiming
that part of native Claims correspondence closed.

v7: exit1,0.524796136s,226372KiB,swap0.
v8: exit1,0.242850733s,176620KiB,swap0. Both retained the2GiB/noSwap caps.

## Exact extracted reference and Lean result

The same Rust owned_step body used by v6 was extracted with only its name
made public in the isolated source copy. Its actual complete QM31/CM31/M31
and all11 default-feature error constructors are emitted; there is no opaque
external type or custom axiom. Charon: exit0,54.218668836s,479836KiB,swap0.
Aeneas: exit0,0.265227771s,61600KiB,swap0. Each used fresh whole-host admission
and a separate1536MiB/2GiB/noSwap/Tasks64 scope. The source and lock stayed
unchanged. Exact tool hashes and native-reference source/receipt hashes bind
the two stages. Raw LLBC is not distributed; source and generated Lean are.

Maintained S1ClaimsOwnedStepTypesV1/FunsV1 remove generated resource-option
lines/advisory comments,rename only the Types import,and append the function's
axiom audit. normalize.py --check verifies the complete transformation.
No function/type body or namespace was replaced or simplified.

S1ClaimsOwnedStepExactV1 proves:

- error_exact: every wire error is returned unchanged with the same state;
- ok_exact: the actual extracted update is TOTAL for p<3,on arbitrary full
  raw rows/states,returning exactly Array.set;
- run_total: induction over a finite bounded-index list composes those exact
  extracted steps,including early errors,without successful-step premises;
- first_error_exact: no remaining step is executed after the first error;
- three_rows_exact: indices0,1,2 overwrite the entire complete carrier with
  the three rows; no initial sentinel/suffix value remains.

The composition consumes normally returned decoder results. It is not an
extraction or refinement of the complete unsafe native loop,allocator or SDK.
The direct input is a full29-column four-word field array,not its arithmetic
value or canonical projection. No coefficient canonicality premise is needed.

Three focused Lean targets:29.390900458s selected wall,max2,257,059,840B RSS,
swap0; six standard-only audits cover the function and five theorem results.
The Types-only compilation has no theorem audit of its own. All jobs used the
atomic local lock,-j1,-M4400,warm objects,one at a time. Existing Array.update_spec
is reused; the small symbolic three-cell overwrite is proved without reducing
any concrete field/recurrence graph. Failed rewrite/dependent-let probes are
retained and excluded. No full or unchanged regression ran.

## Source authority, reproducibility and remaining premises

The native source payload is the adopted25866ec331cc7ce27dd9956609c11d32fa8fa58a
blob,not a silently substituted working file. r1_semantic.rs is wholly equal
across b272/25866; r1_wire.rs has adopted proof-only appended modules,so its
complete adopted blob is explicitly used and pinned. The default record,
decode and error declarations remain the real source types. The compiled
proof/native snapshots retain original whitespace byte for byte. Unchanged
native dependency inputs are referenced by immutable git blobs with exact
SHA256 checks in source-reuse.json, rather than duplicated. The original
native manifest/input hashes are unchanged; only byte-identical inputs are
referenced and all harness modifications remain physical source files.

Evidence is source-only focused-extractor-proof-packet-v1 under
s126-current-caller-20261021/s1-claims-row-step-20261024. The accepted native
manifest is retained unchanged; the extra branch independently pins failed
initializedness probes and successful extraction. The selected Lean closure
has its own import pins. Source-only validation:

```
python3 tools/s1-claims-row-step-20261024/check.py
```

Earlier failures:v1/v2 stopped at Cargo metadata due to omitted retained
workspace/lock setup; v3 had raw M31 constructor type errors; v4/v5 exposed
the early-versus-late lifetime binding required by generic Kani stubs. They
ran no SAT proof. The tautological 'a:'a bound makes the stub's impl lifetime
early-bound; it does not restrict native inputs. No dependency was upgraded
to bypass the yanked unused dev dependency; retained exclusions/lock were used.

Remaining S1 premises are still actual-source Claims allocation,initializedness,
cleanup and full-loop association; concrete Terminal; remaining mask/eta/
terminal domains and native/Std/abort/effect joins. The arbitrary enclosing
FinishModel.Claims/Terminal parameters have NOT been discharged by this local
packet. No generic execution structure is presented as their concrete source
instance. The prior640d3 caller-range packet remains the enclosing progress.

S6's actual SDK/installed-caller integration is unchanged by this helper.
The approved S2 D189 producer should be consumed with the SAME concrete ops
and child marks; no universal input-retention or reconstructed-statement
identity premise is to be reintroduced. Shared release/probability/oracle-law
and artifact joins remain open. No new production adoption decision is
requested; any future source/backend candidate needs explicit equivalence,
integration and re-pin obligations before attributing this evidence to it.
