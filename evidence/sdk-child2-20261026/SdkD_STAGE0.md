# SDK child continuation: stage 0

Branch codex/cx-sdk-child2-20261026; start 728b0649e0. Only SdkD_ modules and
this evidence directory are writable task outputs. No push or merge.

Read the root AGENTS.md including Security and proof discipline, both supplied
scratchpad rules, S2 ownership/plan/diagnosis/interface, the adopted route B
addendum (2026-10-23 01:20), the SdkC/Tx2N/Uni/SInt2 handoffs and predecessor
sources, premise ledger including Uni update, and security contract. Historical
S2 documents resolve under docs/research/100bit-spend-path-20261013/.

Before: Uni_Accepted.accepted_pair_unified still takes an arbitrary
ChildConeJoin plus accepted-only FirstMarks/SecondMarks. Tx2N_Finish.Outcome
still universally requires authenticated_S1 over all 22 folded payloads.
These are implementation obligations, not cryptographic trust.

Plan: construct the literal current TX1 instrumented control computation,
prove all-input erasure and accepted-call sites, then construct the SDK child
and accepted-only marks. Compose on the same cuts, instantiate the global
oracle experiment and root provenance, and use one indexed recovered map
across both batches. SdkC's existing partial-syscall/replay results are reused.

The inherited replay security loss is 6*(Q+1040)^2/256^32, with 1040 extra
queries and the original first-commitment cut retained. It is a security-bound
term, not a logical premise. Instantiating the deployed global source budget
is still required. SessionAPrepare may remain named; no implementation gap
may be hidden inside it.

Budget: 100 Lean attempts including dependency builds; 30 Kani. Each attempt
uses unchanged S2W launchers in the coherent SInt2 host workspace, one module,
-j1 -M7000 -DElab.async=false, MemoryHigh6G/MemoryMax8G/Swap0/TasksMax64.
Initial host inventory: init.scope and one other worker scope. No other job
or source modified. Failed sources and complete receipts are retained.

Freeze: no protocol, parameter, feature, wire, native/Rust or cfg(kani) edit.
Inherited ELF pins: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4;
devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299;
Pool 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.
No ELF rebuild trigger. No wallet/key/account activity. No package replay.
No security target is yet established.
