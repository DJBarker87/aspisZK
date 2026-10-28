# Public reservation before/after

Before: LedgerBody.reservation ran the whole witness-dependent body and read
`after.ledger.entered` only from a returned result. The handoff had no proof
of a common prefix reservation function.

After: PublicReservation.entry reproduces the exact source public_bytes →
map_err → Try branch → prepare → nonce/layout/factor guard order; its arguments
are address, native pub, variant, hash and nonce. It has NO compiled columns or
field-mask-entropy argument. PublicDecision.decision preserves its returned
path and maps machine fail/div to none only for the total boundary DATA field.
For a returned source caller, EnteredCaller.caller / PublicDecision.returned
prove the entry result equals the actual entered path. LedgerPublicEntry proves
the old full-body reconstruction equals this public decision on every returned
body execution; LedgerPublicShape rewrites the exact ledger state equation to
use that decision. No history is assigned to a machine fail/div execution.

These are source/control facts at the full emitted body, for arbitrary compiled
inputs and external dictionaries; no OS success or E1 assumption is used.
Commonness across witnesses requires the SAME source pub/hash/dictionary/nonce.
Those public-input/dictionary identities still need the installed native family.
No equality of compiled witness columns is needed.

| Obligation | Before | After |
|---|---|---|
| full source/header projection | missing | checked (25616/25618) |
| common source-prefix decision | missing | checked (25627/25635) |
| decision = entered path on returned source caller | missing | checked (25634/25635) |
| source ledger equation using public prefix | body reconstruction only | checked (25636/25637) |
| actual native world/E2 realization | premise | premise |
| original residual fields / endpoint fields / runtime,boundary | 6 / 8 / 2 | 6 / 8 / 2 |

Affected rows: source/control sub-obligations of V337 and V161/V162. Whole
native rows V036/V037/V038/V161/V162/V165–V168 remain open. L1 counts/errors
and L2 F3/F5/F6 are not discharged: a complete native observer decoder and
consumed trace/world association have not been installed.
