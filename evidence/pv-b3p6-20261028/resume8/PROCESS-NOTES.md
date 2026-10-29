# D425 process notes

- Same worktree and branch; entry884adf0f9d0a199263bbeef2fd18cb6881a4b6cf.
- External preflight:5673 pinned objects, no mismatches. Retained own cache:
  83 objects byte-equal resume7's frozen inventory.
- Initial uncharged input-preflight failure: missing PublicSuccess227 object;
  restored its five exact recorded predecessors privately, smallest first.
- Rejected62308: the new namespace's `ok` theorem shadowed Result.ok in the
  copied optional-recipient expression. The generator now qualifies Result.ok;
  changed source62309 passes. No failed unchanged source was retried.
- Admission refusals use the existing run.py guard and existing serial
  continuation tool; each refusal observes the full180-second cooldown before
  fresh admission. IDs remain reusable until a compiler actually starts.
- Some early read-only SSH cache/receipt diagnostics ran while the serial
  runner connection was still open. No second capped scope ran. Thereafter
  diagnostics are deferred until that runner returns; no ControlMaster is used.
- New sources contain no limit overrides, sorry/admit/native_decide,
  implemented_by, axioms, or XR imports. Superseded uncompiled flat-sequence
  and older rejected candidates earn no credit.
