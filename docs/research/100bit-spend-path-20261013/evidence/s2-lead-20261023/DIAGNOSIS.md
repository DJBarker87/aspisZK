# Stage 1: v7 conditional SDK bridge diagnosis

S2 remains open. This is inspection of retained evidence, not a new Kani
proof, a replacement adapter, or a claim of an SDK defect.

## Decision

The proposed **representation contract is insufficient for contextual
substitution**. Its intended shared-borrow counter transition is sensible,
but byte-array havoc plus integer-word equalities does not establish that
the returned typed `Ref` owns the very same counter that was incremented.
The selected trace satisfies those postconditions and then violates that
identity in the actual typed destructor context. Do not install this contract.

This distinguishes an inadequate encoded contract from real SDK behaviour.
The retained SDK source (`../s126-current-caller-20261021/sdk-live-out/
sdk-original-lib.rs`, lines 121–131) delegates directly to `self.data.try_borrow()`
or `try_borrow_mut()`, mapping borrow errors to `AccountBorrowFailed`.
The counterexample bridge instead has `#[kani::stub_verified(sdk_out)]`;
it does not execute that acquisition. Moreover the corresponding actual
contract check has not passed. The word `verified` in the annotation is
not evidence of a completed callee proof.

## Trace, with exact line anchors

All log line numbers below refer to
`../s126-current-caller-20261021/sdk-live-out/receipts/
sdk-live-out-shared-bridge-counterexample-v7/stdout.log`.
Source line numbers refer to the retained
`sdk-live-out/sources/sdk-live-out-shared-v7/src/lib.rs`.

| Log lines | Observation | Significance |
|---|---|---|
| 53252–53269 | `initial = 0`, source line 67 | This restoration witness starts with an ordinary unborrowed counter. |
| 63098–63115 | `before = 0`, contract closure | The saved pre-state agrees with the harness. |
| 63803–63820 | `now = 1`, source line 9 | The postcondition observes the intended increment. |
| 64816–64833; 65418–65435 | First raw word is `562949953421336`; comparison `var_21 = TRUE`, source line 12 | Integer equality to the data-value address is satisfied. |
| 66555–66572; 66974–66991 | Second raw word is `562949953421328`; conjunction `var_0 = TRUE`, source line 13 | The integer counter-address test and complete success predicate are satisfied. |
| 67373–67387 | Typed `result.Ok.0.borrow.borrow` is reported `unknown`, source line 69 | The trace printer supplies no concrete typed pointer identity. Do not invent one from the integer above. |
| 68117–68134 | `BorrowRef::drop` reads `borrow = 0`, pinned `core/src/cell.rs:1551` | The typed destructor does not observe the counter value 1 required of this acquired borrow. |
| 68290–68336 | Checked subtraction at `cell.rs:1553`; overflow flag is false in this selected trace | Here it subtracts from 0. This selected restoration witness is **not** an overflow witness. |
| 69166–69183; 69228–69245 | The account counter still reads 1 after Drop | The expected restoration to `initial = 0` did not occur. |
| 69273–69284 | `proofs::actual_sdk_out_bridge.assertion.10` fails, source line 71 | The proposed contract fails its caller's destructor context. |

The ordinary full bridge log (`sdk-live-out/receipts/
sdk-live-out-shared-bridge-v7/stdout.log`, lines 12–19) separately records
two failures out of 830: subtraction overflow in `BorrowRef::drop` at
`cell.rs:1553` and counter restoration at harness line 71. Only the latter
has this selected-property trace. It would be unsupported to claim that the
selected trace sets the destructor counter to `isize::MIN`, or that it
demonstrates both failures with one valuation. No new trace is needed to
reject the contract: the ordinary initial-zero witness already does so.

## What was encoded, and what was missing

Source lines 6–16 require an initial `Err(AccountBorrowFailed)` output,
allow modification of an output **byte array** and the account counter,
then inspect the havoced bytes as `Reply = Result<Ref<...>, ProgramError>`.
For `Ok`, they require `0 <= before < MAX`, `now = before + 1`, a two-word
guard size and two raw `usize` equalities. The body at lines 17–18 really
writes the SDK result, but the bridge at lines 52–70 replaces it with this
contract. Moving the typed result and dropping it remains actual code.

The missing assertion is not another numerical bound: it is the semantic
relationship between valid typed Result/Ref fields, their pointer
provenance, the lifetime of the RefCell allocation, and its live borrow
ownership. Integer address equality does not supply that relationship.
The trace establishes insufficiency of this encoding under the pinned
Kani/CBMC translation; it does not uniquely identify a Kani compiler defect,
prove a universal Rust layout, or exhibit a safe native SDK execution with
this behaviour. The intended SDK rule would require Drop to read 1 and
restore the same counter to 0 here.

A future route A must first establish typed, provenance-preserving guard
acquire/move/deref/drop identity in a small context, including the error arm,
before enlarging the caller. It must not assume restoration as the desired
caller conclusion or fabricate a foreign guard from bytes. Route B would
make these library semantics explicit trust, subject to an owner decision;
it does not turn v7 into proof evidence.

## Evidence and scope

The selected receipt pins source revision
`d8fc9db732c70ef8dd1dd548184326318d5e1ad1`, CBMC 6.8.0,
the exact GOTO filename and argv: exit 10, 0.803 s, 108008 KiB peak RSS,
zero swaps; limits 6G high / 8G max / swap 0 / 64 tasks.
The enclosing failed Kani receipt remains excluded. Multiple historical
metadata candidates are not resolved into a new authoritative GOTO pin here.
No prover, Rust compilation, source adoption, ELF rebuild or Lean axioms audit
ran in this stage. `#print axioms` is not applicable to source/log inspection.
