# TX2 query: incomplete delivery

**Neither saved_ten nor twelve is discharged. No Tx2Q_Accepted theorem was
produced. No counterexample against the concrete shipped implementation was
established. S2 / the release target remain open.**

Branch codex/cx-tx2-query-20261025. Stage 0 commit 7b87ac4542.
No push, merge, production edit, candidate edit or other-worktree edit.

## Exact checked result and its limit

`AspisR1.Tx2Q_Obstruction.accepted_without_state_laws` executes the existing
parameterized extracted authenticated TX2 body on Op3I_Witness.proof, with
Tx2I's actual concrete shape and finish installations. It specializes the
remaining operations using Tx2I_Witness.fixture. It proves source acceptance,
the exact op18 return, exact op6 return (for every g), exact op9 return, and
failure of both state equations on those returned states.

Countermodel: resumed power 0 / rhs 1, returned power 0 / rhs 0, model rho 1.
The model saved power is 1^10=1, whereas resumed power is 0. Twelve model
steps from zero power retain rhs 1, whereas the returned source rhs is 0.
`Tx2Q_StateObstruction` uses run_power and symbolic induction, not evaluation
of a concrete recurrence. The flush is identity and its mutable Vec back
materialization is definitionally the returned Vec.

This refutes **acceptance alone implies the state laws for every free stage
dictionary**. It does NOT refute the desired concrete implementation theorem:
it does not establish a TX1/D189 pair, RowOrder history, the retained full
FinT owner laws, or production interpretation of the fixture leaf operations.
It supplies no shipped-source defect claim. This is narrower than the owner's
requested deliverable and receives no saved_ten/twelve closure credit.

Non-vacuity of this narrow statement: source acceptance is a proved output,
not a premise. The fixture is constructed from arbitrary base/prepared/state/
geometry/pending carriers, and the proof works for every data/q without a
logical hypothesis asserting either model law. This is NOT joint inhabitation
of the entire accepted-pair/runtime/cryptographic interface.

## Before/after and premise audit

Before: Tx2I_Accepted.accepted_pair_claims_tx2, unchanged in lean/Tx2I_Accepted.lean.
Its finish continuation still has saved_ten and twelve exactly as recorded in
evidence/tx2-install-20261025/before-statement.lean.txt and after-statement.lean.txt.
After: **no replacement accepted-pair statement**; no premise removal claimed.
No quantifier, carrier, failure event, conclusion, arithmetic hypothesis,
security assumption, or trust boundary was changed in an existing theorem.
The new narrow countermodel has different scope and is explicitly not a
weakening/equivalent replacement of that theorem.

Concrete unresolved joins identified by source inspection:

1. Tx2I installs shape/finish only; op18/op6/op9 remain in stageBase. The actual
   TX1 current-caller installation likewise retains its op7 query, op16 writer,
   op17 flush, op18 pending and op19 geometry. Port5Q2_Checkpoint.accepted instead
   requires its specific VTop dictionary and the SAME writer-returned Vec.
   A nominal/source-control bridge from the actual TX1 installation to that
   dictionary was NOT constructed. Byte history alone proves no body arithmetic.
2. RowOrder_History.on_d189_cuts can be applied to the same exported cuts;
   its writer/reader cone premises concern header hashes and length only.
   They do not assert or prove the arithmetic saved-state identity.
3. Port5Q1_Block/Complete require parsed.wire=bytesOf proof, matching source
   preparation/query/rho, indexed packed-map opening authentication, actual
   geometry/pending/query calls and canonical resumed fields. These were NOT
   derived for the exported TX2 arguments. The theorem's universal parsed/q/tr/i
   binders are not automatically the source parser's own selected witness.
   These cannot be replaced by a new ObservationBinding, body equality, or
   twelve-step premise under the requested premise-removal audit.

Next concrete deliverable: a checked SAME-return nominal TX1-to-Q2 installation
bridge, then derive Q1's actual source bindings and authentication and compose
on those exact cuts. Neither bridge nor full conditional closure was completed.
The interface countermodel does not authorize abandoning that feasible route.

## Validation and section 6 target freeze

6/80 Lean attempts, including zero dependency builds; 0/30 Kani runs.
Attempts 001/003/004 are ordinary elaboration failures. 002 hit the default
200000-heartbeat limit; it was split into a separate symbolic state module.
It was not rerun unchanged. No timeout command expiry or memory kill occurred.
Failed source snapshots/logs (including failed sorryAx diagnostics) are retained
and receive no proof credit. No heartbeat/depth/cap increase.

Final accepted targets:

| Attempt | Target | Exit | Wall seconds | Peak RSS KiB | Swap |
|---|---|---:|---:|---:|---:|
| Tx2Q-005 | Tx2Q_StateObstruction.lean | 0 | 2.528871928 | 4269948 | 0 |
| Tx2Q-006 | Tx2Q_Obstruction.lean | 0 | 2.263347632 | 5160980 | 0 |

Source revision for both: 7b87ac4542693d887e6be88cebb9347dedc271f4, with new
source files dirty; exact source hashes and snapshots in each attempt.
Every new top theorem has a final #print axioms containing exactly
[propext, Classical.choice, Quot.sound]. Receipts record exact command, target,
revision, source hash, direct dependency/object and Lean binary hashes, exit,
wall, RSS, swap, verified cgroup and limits. validation-summary.json checks
snapshot/final-source hashes and the passing axiom/cap/swap evidence.

Used the coherent sound-int2 workspace and its unchanged S2W launchers.
Every attempt ran lake env lean -j1 -M7000 -DElab.async=false in its own
systemd scope: MemoryHigh=6G MemoryMax=8G MemorySwapMax=0 TasksMax=64.
No other job/source/object was replaced. Initial host inspection had no other
build scope; final inspection showed another worker scope, left untouched.
All owned jobs are terminal. No infrastructure implementation was changed.

No runtime/protocol parameters, wire format, features, extraction, toolchain,
key, native/Rust/Kani/SBF artifact changed. No package/manifest replay or ELF
rebuild ran. Historical pins are inherited only, not reconfirmed:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

Focused object hashes/sizes, no committed binaries:

- Tx2Q_StateObstruction.olean: 82344 bytes,
  6cfb7bec2e2a368996fc96516940ddec238cf14f94dea658bb586840786936e6
- Tx2Q_Obstruction.olean: 59144 bytes,
  de5b4e7e92d1566e473e6dca4480cb41b307a1b91e3ab8e7ab84e4be2e8c75e5
