# ABI map v4 resource-option-clean source evidence

ABI map v3 Types carried generated `maxHeartbeats 1000000` and `maxRecDepth 2048` options. V4 removes only those two directives and their two corresponding explanatory comments. The checker records that all remaining Types source bytes are identical; the ABI-map proof source is byte-identical and was recompiled against the v4 Types owner.

The Types and proof phases each passed a fresh admission and compiled with the standard runner (`-j1 -M 4400`, High1G/Max2G/Swap0). Types source SHA `d8362a2a37393cb861f99225dbbae30ea7b5464293a9a57da4c6321baa14e12e`, object SHA `e1023b14baee6a4bde62e897b47f8694f002ef17e5d3a79bf0f1488e00d11d3b`; ABI map source SHA `78960427f98f739afb1e9132f6eef4a78f310fb1ae985e41aeab357eaea276b2`, object SHA `05dcc442bc571e538335aca8cdc8c54b028f9175196dfe33b272f312ff462b64`. Both exits 0, no scope swap or memory events. Detailed preflight, command, time, and receipts are retained under `attempt/`.

Compiled objects are intentionally omitted. `manifest.json` hashes all source/evidence files. The old v3 Types/ABI map proof receipt remains historical evidence only; use v4 object pins for this closure.
