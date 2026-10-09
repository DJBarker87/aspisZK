# Gamma origin-history adapter — 2026-09-12

`lean/FSV8GammaOriginHistoryAdapter.lean` proves the strongest history lift
available from the existing alignment. `projected_event_lifts_to_v7_record`
maps an FS log event through `StateAligned.history` to a concrete V7
`QueryRecord` in the V7 history.

The adapter intentionally stops there: `projectRecord` erases the V7 actor,
so it cannot establish that the lifted record is an adversary query and hence
belongs to frozen `q1`. The separate
`origin_q1_membership_from_lifted_record` theorem consumes exactly that actor
classification plus equality with the origin's state-at-adversary-halt, then
uses the gamma boundary configuration to obtain fixed-record q1 membership.
No actor or origin-cut equality is invented, and no programmed-target,
freshness, acceptance, ROM, or probability claim is made.

Evidence: `results/gamma-origin-history-adapter-v1/report.json`.
