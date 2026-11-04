# Candidate rows: ADDED-PENDING-LEAD, none assumed

This is an obligation inventory, not a contract amendment. The existing
RuntimePersistence, RuntimeReturnData (nonempty) and RuntimeMemcmp rows remain
unchanged and accepted. No whole-history, owner/balance preservation,
all-syscalls-return or oracle-order row is adopted.

## NGP-R1 RuntimeClockSlotBinding — ADDED-PENDING-LEAD

Exact candidate successful-value law (Lean notation, no axiom declaration):

```lean
-- Context, clockGet and bankSlot are supplied by a pinned runtime projection.
-- U64 is the current S2W_ExtractionBoundary.Slot carrier.
∀ (ctx : Context) (v : Aeneas.Std.U64),
  clockGet ctx = Aeneas.Std.Result.ok v → v = bankSlot ctx
```

`clockGet : Context → Result U64`, `bankSlot : Context → U64`.
Bind ctx to the SAME instruction executing adapter process; native caller
must associate Clock::get()?.slot (r1_pool_adapter.rs:910) and every forwarded
current_slot with v. The proposed row says nothing about successful return,
strict growth between transactions, epoch changes, or retention of accounts.
Current CPG observations do not encode this projection and RuntimeSyscall is
hash-only. It may be unnecessary as NEW trust if the lead locates an existing
accepted sysvar/platform realization covering this exact call, or if a pinned
runtime proof supplies it. Until then: OPEN, not assumed by NGP_L159_statement.
Consequence of acceptance: one explicit runtime value trust row; rejection:
prove the pinned Clock sysvar realization or keep Pool slot gates conditional.
No owner choice is made here.

## NGP-R2 RuntimePhysicalObservationRealization — ADDED-PENDING-LEAD review item

The exact association target is the conjunction of these equalities for the
same physical bank/transaction projection p, not a proposed blanket trust:

- `p.next t u` describes consecutive executions on one bank lineage;
- `CPG_Projection.before p t key` is the actual loaded starting data/lamports;
- `CPG_Projection.tentative p t key` is the actual final tentative data/lamports;
- `CPG_Projection.success p t` is the actual final PARENT status;
- `CPG_Projection.loaded p u key` is the next entry's actual loaded Option bytes;
- `p.physicalEvents t/u` and `p.actions t/u` are the actual ordered actions;
- both layout handles and CPS_PhysicalKey identify the actual account objects.

These are game a–d / runtime entry realization and native caller facts, with
CPH_Game's exact expanded type in NGP_L008/stdout.log. They are NOT covered
merely by constructing a model `Observations` value. The game already approves
the physical meaning of its fields; no additional trust should be necessary
IF the existing game/entry realization proves the projection. Marked
ADDED-PENDING-LEAD solely so an attempted expansion of runtime trust cannot be
hidden. Preferred route: prove source/account projection, add NO trust row.
If a new runtime projection assumption is proposed instead, lead must specify
its exact pinned carrier and disjoint scope before adoption. It cannot include
L159, source success, arbitrary no-writes, or oracle transport as its conclusion.

## Explicit non-candidates

Syscall totality is not required by the current partial model; NGP_L181 keeps
the failed/diverging call and ideal suffix. A new ReturnsOnly-for-all-runs law
would exclude real exits and is NOT proposed. CPI argument order, no
intervening CPI/set_return_data, exact792 bytes, owner/marker/funding checks,
ordinary CP eligibility, writable/account/borrow frames and settlement
association are native caller proof obligations under existing trust.
Oracle schedule/dedup/rejection transport is mathematical/source work, not a
cryptographic assumption or a new runtime trust item.
