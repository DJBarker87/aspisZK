# Row shape / scan preflight

Read the binding root AGENTS security/proof discipline, common and local Lean rules,
S2 ownership handoff, lead plan, diagnosis, S2LeadInterface, SOUND-INT port table,
SInt2 handoff, C3-BIN route B adoption and 25 October 13:35 ruling.
Historical S2 files resolve under docs/research/100bit-spend-path-20261013/.

Only RowShape_ new modules and this receipt directory will be written. Session A
sources are inspected via immutable git revision d346dc7cb7232f12c4ff930d1e2db320bdc101d9.
No shipped source changes, no keys touched, no ELF rebuild trigger. Inherited ELF
pins are f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4,
63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299,
121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548;
not freshly reproduced. Parameters, features, wire format and toolchain unchanged.

Host read-only preflight: coherent workspace exists, no populated build scope
besides init.scope at inspection. Each focused compile will reuse that workspace
and its pinned objects, one module per scope, -M7000, MemoryHigh=6G,
MemoryMax=8G, MemorySwapMax=0, TasksMax=64. No infrastructure changes.

Initial source finding: CurrentCaller op3 and op4 are supplied functions. The
Claims installation appears to preserve them. Next deliverable: checked exact
projections and a source counterexample if this prevents the requested universal
interpretation. No assumption discharged, added or changed. No formal result yet;
exit/wall/RSS/swap/axioms are inapplicable at this read-only stage. Budget 0/100
Lean, 0/60 Kani. S2 and the 100-bit target remain open.
