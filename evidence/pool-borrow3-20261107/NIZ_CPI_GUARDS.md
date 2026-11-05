# NIZ held-guard boundaries

Target not yet established; all four sites OPEN. No intersection has been found in the inspected source layouts; this is not a native reached-path certificate. RuntimeCpiReadonlyEntry7 is unused.

| Site | Source layout and Lean fact | Missing native facts |
|---|---|---|
| pair_forest deposit | fresh/same guards 1,2 and token_start=3; rollover guards 1,3 and token_start=4; passed offsets 1,0,3,2,4. NIZ_LAYOUT.deposit_separate. | Successful all-account uniqueness; same reached keys/cells, exact helper/CPI arguments and deployed runtime. |
| pair_forest terminal | cursor 4 for genesis/same and 5 for rollover; guards 2,3 or 4 plus cursor; passed cursor+7+[1,0,2,3,4]. NIZ_LAYOUT.terminal_separate. | Successful planner/uniqueness and dominance; same reached argument/cell map. |
| pair withdrawal | pool 0, selected history below marker, marker; passed marker+5+[1,0,2,3,4]. NIZ_LAYOUT.pair_separate. | Actual plan_layout/require_unique packet, bounds and same-state native association. |
| transition before_persist | Deposit source rejects cross-group equal keys; withdrawal held indices precede marker, while marker reads/writes and marker/payer/system CPI plus token accounts are at/after marker; private-transfer callback is no-op. NIZ_LAYOUT.withdrawal_callback_separate and deposit_callback_key_separate. | Per-deployed-instantiation native footprint under (al), including marker classifier, creation, delta read and marker write; actual group/layout association. |

NIZ_LAYOUT.entry_cells_separate and entry_footprints_disjoint consume the exact seven-field AdapterRw.RuntimeEntrypointAdmission approved for Pool under (ap). They establish entry-map cell separation only. No native preservation of that map or callback frame is silently assumed. DISCHARGED requires all three requested facts on the same reached execution; none is labelled DISCHARGED at this stage.
