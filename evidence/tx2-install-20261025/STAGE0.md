# Authenticated TX2 installation scope

Base: 87a79f0184316e40b99d19999669122b63362ae4.
Branch: codex/cx-tx2-install-20261025. Prefix: Tx2I_.
Budget: 80 Lean attempts including dependencies, 40 Kani runs.

Install only adapter op11 to VTop_Model's extracted authenticated TX2, with
stage op3 the existing Op3I_ source body (nominal carrier transport) and stage
op19 the FinT_Model source finish. Preserve the Op3I_Accepted chain and all
other adapter/current-caller slots and premises. D188 remains the sole native
association. Derive cuts from the same accepted pair, then apply the unchanged
named FinT_Model hypotheses to the actual reached state.

Read S2 ownership/plan/diagnosis/interface under the historical research root,
C3-BIN 2026-10-23 01:20, current Op3I/FinT/SInt2 handoffs and verifier-top plan.
No shipped-file change is planned; inherited ELF pins are not rebuilt evidence.
Only standard Lean axioms allowed. Existing SInt2 host workspace and unchanged
S2W launchers will be reused, with one module per 6G/8G/swap0/tasks64 scope,
-j1 -M7000. No package replay. No key operations.
