# NIZ held-guard boundaries

Target not yet established; all four sites OPEN. No intersection has been found in the inspected source layouts; this is not a native reached-path certificate. RuntimeCpiReadonlyEntry7 is unused.

| Site | Source layout and Lean fact | Missing native facts |
|---|---|---|
| pair_forest deposit | fresh/same guards 1,2 and token_start=3; rollover guards 1,3 and token_start=4; passed offsets 1,0,3,2,4. NIZ_LAYOUT.deposit_separate. | Successful all-account uniqueness; same reached keys/cells, exact helper/CPI arguments and deployed runtime. |
| pair_forest terminal | cursor 4 for genesis/same and 5 for rollover; guards 2,3 or 4 plus cursor; passed cursor+7+[1,0,2,3,4]. NIZ_LAYOUT.terminal_separate. | Successful planner/uniqueness and dominance; same reached argument/cell map. |
| pair withdrawal | pool 0, selected history below marker, marker; passed marker+5+[1,0,2,3,4]. NIZ_LAYOUT.pair_separate. | Actual plan_layout/require_unique packet, bounds and same-state native association. |
| transition before_persist | Deposit source rejects cross-group equal keys; withdrawal held indices precede marker, while marker reads/writes and marker/payer/system CPI plus token accounts are at/after marker; private-transfer callback is no-op. NIZ_LAYOUT.withdrawal_callback_separate and deposit_callback_key_separate. | Per-deployed-instantiation native footprint under (al), including marker classifier, creation, delta read and marker write; actual group/layout association. |

NIZ_LAYOUT.entry_cells_separate and entry_footprints_disjoint consume the exact seven-field AdapterRw.RuntimeEntrypointAdmission approved for Pool under (ap). They establish entry-map cell separation only. No native preservation of that map or callback frame is silently assumed. DISCHARGED requires all three requested facts on the same reached execution; none is labelled DISCHARGED at this stage.

## Native/model work at the seven barriers

K011/012: original deposit uniqueness-call barrier bb152 dominates candidate exclusive stores bb178/bb180. K013/014: terminal planner call bb15 dominates stores bb180/bb182/bb184. K015/016: pair-withdrawal uniqueness call bb125 dominates stores bb158/bb160/bb162/bb164. K030/031: terminal planner uniqueness call bb67 dominates its successful layout construction bb69. K032/033 and K034/035: the ordinary and prevalidated deposit cross-group checks dominate transition calls. K036/037: withdrawal whole-account uniqueness dominates its transition call. Every positive has a failing control removing the barrier mark on its actual outgoing edge; all edges include normal/error/unwind branches. NIZ_Dominance supplies finite-prefix induction. These are CFG certificates, not an assertion that candidate SDK stores are already bound to the correct physical cells or that all caller/child frames are proved.

K028/K029 checks the actual Rust ? dispatch on both original uniqueness unit/error arms and the absence/presence of its continuation. K009/K010, K023/K024 and K025/K026 remain conditional on the OPEN original key-comparison/source pairing in NIZ_STUBS.md; their mathematical row/prefix/cross-group conclusions are proved by NIZ_Unique/NIZ_Groups, not promoted to whole-helper/native success facts.

The capture-free no-op before_persist literal at transition.rs:864 has local reply/frame PASS K017, matched frame/reply FAIL K018/K020, and identical-verdict rename check K019 under (al). NIZ_Noop records its empty model footprint and empty scope. This covers that instantiation only. Deposit/prevalidated-deposit and withdrawal native footprints remain OPEN, including marker rechecks, possible marker creation, token CPI, delta read and marker write.

All four top-level held-boundary units remain OPEN. No reached index intersection or production liveness failure has been established. No site is labelled DISCHARGED using an assumed frame or incomplete callee.
