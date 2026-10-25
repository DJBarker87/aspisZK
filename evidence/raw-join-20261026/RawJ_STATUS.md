# RawJ L157 work

Branch codex/cx-raw-join-20261026. L157/L182 OPEN. L159 excluded.
Budget: 0/100 Lean attempts; 0 Kani authorized. No package replay.
Only RawJ_ modules and this receipt directory may change.
Host workspace: /home/dombarker/project-offloads/codex-cx-sound-int2-20261025.
Existing S2W launchers and GExp_/GExq_ objects reused.
All Lean uses -M7000, MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64.

## Freeze
No shipped source changes. Artifact pins inherited, not newly reproduced:
default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Initial inspection
The requested older design/DIAGNOSIS/interface paths resolve under
docs/research/100bit-spend-path-20261013/. Security and proof discipline,
common rules, local-lean rules, both global-exp handoffs, SInt2 handoff and
route B adopted addendum read. Native wrapper model allocates/copies/cleans
without oracle reads; the containing original account body still needs its
own all-outcome count. Inner 1921/2961 is not transferred as an account bound.
