READY-AGG: driver-only repair validated; stop before any 16 GiB admission.

Branch: codex/pv-evhc-20261029. Resumed from b1c3f49bf7. Recovery committed as bc3a9072d1; driver and preflight sources committed as 2f698fcb028. Exact future three-step command, single-scope runner invocation, admission procedure and required validation are in READY-AGG.md. Driver adaptation was unavoidable because the original accepts only fixed selectors. Full diff is DRIVER.diff: ONLY module names/root names change. NEP_WALKER.lean is unchanged from research. No audited module was changed.

Host inventory found no surviving task scope/process and no use of 92070. Recovered evhc7 receipts and validated local content pins and source snapshots before proceeding; see RESUME-VALIDATION.json and recovered-evhc7/. Previous scope 92060 remains failed and spent. No work was duplicated.

Normal scope pv-evhc9-92070.scope: exit 0; wall 7.035104208858684 s; peak RSS 3,580,352 KiB; swaps 0; cgroup peak 2,249,052,160 bytes. MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 64; Lean -M7000. Source revision 2f698fcb028. Full commands, hashes, metrics and summary-based #print axioms are in lean-92070/receipt.json, PREFLIGHT-STEPS.json and per-step logs. The aggregate runner's print_axioms field is empty because the sequence stores compiler output in those per-step logs; RECEIPT-VALIDATION.json collects all full summary lines.

All NEP eight planted/mutated cases passed with exact expected axiom sets; two additional private-constructor/theorem-body cases passed. Reachable-name lists confirm match_N, private definitions, auxiliary definitions, theorem bodies and inductive constructors were traversed. The missing-constant negative control produced NEP_FAILURE and exit 1 as required, and the enclosing test sequence passed. It tests an unresolved root; the unchanged walker's same lookup handles descendants. These are intentional planted axioms, not release-audit results.

One authorized preflight scope used; no remaining scope budget. No 16 GiB admission requested or scope launched. Aggregation sequence preparation was syntax-checked only. The prior consumer compile and full coherent scan are reused as historical evidence; they were not rerun. Full combined raw audit remains NOT_RUN, including matching both soundness roots in the privacy environment.

No premise removed, added or changed. FixturePdaRuntime base remains; event acquisition and joint simulation links remain open. Privacy target not yet established. Next deliverable: after Stream A authorization, lead runs the documented single agg16 sequence with a fresh ID, verifying every object and companion pin first.

Unrelated pre-existing pv-dup changes were retained untouched and excluded from these path-limited commits.
