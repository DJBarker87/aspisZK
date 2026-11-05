# Retained failing steps

No timeout, memory kill, cap increase, Kani or extraction attempt so far.

- L001/L002: canonical nominal constructor aliases do not export constructors
  through their alias namespace. Fixed explicit Variant/Error/Phase owners in
  the NHT retarget map. L004 passes the intermediate common body.
- L003: own-input prelaunch failure: missing predecessor object. No scope or
  Lean launched. The complete traceback is the local tool result; admission
  retained. Continued after repairing and compiling predecessor.
- L005/L006 replace the intermediate port with exact emitted transparent
  constants/standard helpers. This is a source change, not a repeated replay.
- L007: own retarget script imported Constants instead of EmittedCommon after
  header repair. Fixed import; L009 passes.
- L010: rewrite left a reflexive goal; added explicit rfl. L012 passes.
  Failed L010's sorryAx output is EXCLUDED, never an accepted proof.
- L017: missing local E abbreviation in the new round adapter; fixed explicit
  canonical carrier abbreviation. L018 then failed before submission on the
  absent predecessor object. No theorem/object from either failure is accepted.

All failed candidates and exact snapshots are retained in attempt directories.
