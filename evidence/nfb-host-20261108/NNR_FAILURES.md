# Retained attempt diagnoses

Each failed source/log is retained under its attempt, excluded from delivery.
No failed attempt was rerun unchanged or with increased caps/timeouts.

- L011: ambiguous run due Lean.Tactic namespace; L012 qualifies the writer run.
- L015: whnf heartbeat while trying rfl on the Merkle case; L016 splits every
  event constructor explicitly and never reduces that Merkle reference.
- L017: map equality simplification did not unfold local o'; L018 explicitly
  unfolds that local definition before applying the named actual-event equality.
- L020: dependent inversion of a computed End failed; L021 generalizes the
  outcome, splits the parser, and then eliminates the resulting constructor Eq.
- L022/L023: outer-constructor inference (first an unknown existential event,
  then unpinned oracle) failed twice. That inference shape is retired. L024
  isolates an explicit, generic @NMN_064.Native.observed constructor with all
  oracle/frame parameters; L025 consumes its named theorem, with no guessing.
- L028: host_shape header left Tx implicit; L029 pins Tx before elaboration.

There were no process timeouts, memory kills, transport failures or reservation
waits in the 30-scope receipts. One transient local tool-call JavaScript syntax
error preceded any launch and was corrected without changing the task.
