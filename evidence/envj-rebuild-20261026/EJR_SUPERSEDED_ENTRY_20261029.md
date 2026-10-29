# Superseded inventory entry (lead note, 2026-10-29)

`EJR_final-inventory.json`, `EJR_INVENTORY.md`, `EJR_all-restored-sources.json` and `EJR_exhaustive-*.json` pin `R1Z.PrivacyR1HeadlineV2` at source sha256 `4321909f01b6...`, the version before commit e030a78a73 ("Remove the redundant closed-goal tactic from the fibre adapter"). Fresh elaboration of that version fails ("No goals to be solved", Stream B attempt 64501); the fix deletes one `rfl` after a `simp only` that already closes the goal, so only the proof text differs and the statement is identical.

Authority: the tracked source `0bb8dcc74e6d...` (research and the privacy candidate), from which the cached cohort was built, following Stream B ruling h5'' (LOG D452) after a mechanical statement-identity check. The EJR files are retained unchanged as historical evidence. Any future replay selecting modules from this inventory must substitute the tracked variant for this one entry.

Use in the soundness release: none. The L188 manifest (evidence/native-l188-20261028) lists the EJR files only as hashed evidence; neither the RPx headline closure nor the NDO_/NDR_ witness reconciliation imports R1Z.PrivacyR1HeadlineV2.
