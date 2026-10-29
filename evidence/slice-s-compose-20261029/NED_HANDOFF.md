# NED work in progress

Inventory stage. No composed row CLOSED. No shipped-file change, ELF rebuild,
Kani or Lean compile at this stage. No keys touched; no push.
Exact stage claims: frozen slice/ledger inventory only; assumptions unchanged.
Next deliverable: actual lower codec substitution and per-edge certificates,
then conservative ledger extension and missing/wrong-certificate controls.

Stage 2: lower emitted codec hypotheses are discharged (NED_L028); SAME
live/after canonical-call domains compile (NED_L030). Full statements and
axioms are in NED_COMPOSED.md. Native state/effect composition remains OPEN.
All 26 unchanged missing codec dependencies passed private capped builds.
One changed-source repair follows an excluded missing-namespace error (L029).
NED_validate.py runs the original NDT invariants before and after its added
certificate checks. Nine controls currently pass, including missing/wrong edge
certificates and exclusion of model-only evidence. No composed row promoted.
