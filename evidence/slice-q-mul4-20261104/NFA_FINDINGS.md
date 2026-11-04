# NFA findings

Audit interface: unchanged NEP_Driver hard-codes non-NEV roots. The NEP_WALKER traversal will remain byte-identical; permission to adapt only driver root/module lists is pending. No strengthened audit pass claimed yet.

NFA_L047: strengthened runtime audit of NEV_DotResult failed at the fixed -M7000 threshold (excessive memory consumption in interpreter). No roots in that group earned credit. No unchanged rerun or cap increase permitted. Receipt NFA_L047/receipt.json and stdout retain the exact failure. Isolate a root / reduce driver startup retention before another attempt. Other module groups continue independently.

NFA_L049: the separate NEV_ActualDotStep group hit the same import/interpreter memory boundary before a reachable graph artifact was produced. Stop interpreted full-caller groups; replace startup mechanism with a compiled runtime driver, without changing the walker. No failed group earns credit.

NFA_L065 excluded: resource API required explicit Lean.Shell import. L066 linked the prior L063 C artifact, so this binary is EXCLUDED (not executed), and will be replaced from a successful fresh source compile. Own script sequencing corrected; no host infrastructure changed.

L067 excluded: Lean.Shell resource API is private in the Lean4 module system; requires import all Lean.Shell. L068 again linked the old C artifact and is excluded without execution. Dependent linking is now gated on the preceding compile result, not merely process completion.
