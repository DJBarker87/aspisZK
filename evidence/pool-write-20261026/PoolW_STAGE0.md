# PoolW stage 0: ASC8 source-certificate scope

The phase-1 target is the actual AS8C (P1) planner/encoder output copied AFTER optional System CPI, under the same physical checkpoint key and canonical committed action. ASC8 is not verifier CP: no verifier CPI or native TX1 child is present in P1. The CP child/copy results are reused separately; they do not describe AS8C output.

Read the mandatory S2 ownership/lead/interface/diagnosis and route-B addendum, complete Pool lifecycle design, SInt2 and Hist_/Hiq_/Hir_ handoffs. Required S2 files reside under docs/research/100bit-spend-path-20261013/. Option B is adopted. Route-B SDK borrowing excludes CPI; existing runtime ownership/CPI/syscall semantics remain external trust. No new runtime item adopted.

Stage plan: isolate actual pure planner/codec extraction; prove the freshness guard by P6 or isolated extraction; compose the write kernel with ordered child effects/errors, then export physical-key/action certificate. Phase 2 alternate-handler frames and runtime history instantiation are separate jobs. No history-only wrapper will be claimed as source closure.

Freeze: PoolW_FREEZE.json pins source revision and all selected inputs. No shipped-source modification, artifact rebuild, new proof, runtime action, account/key operation or security finding at this stage. Lean 0/100, Kani 0/40. Formal release target/exit/wall/RSS/swap/axioms: not applicable, no run. Inherited ELF pins remain f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4 / 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299 / 121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No full replay planned.

Global premises removed: none. S2 and deployed target remain open. No assumption weakened, bundled as discharge, or added. All native/source/P6/SDK/runtime/artifact/history joins retain their existing status until checked here.
