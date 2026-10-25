# Log alignment handoff

Branch codex/cx-log-align-20261026. Scoping complete; no push or transport.
Decision document: design/LOG-ALIGNMENT-20261026.md.

Main results:
- RawK's source-vs-terminal-decision obstruction stands, but the actual complete
  frozen2 verifier has a sampler prefix. Checked verifier_initial_head proves
  its first query is the semantic initialization frame, not a batch leaf.
- Source and full-model inspected orders match at the grammar level, retaining
  115 transcript calls, all eight query pairs, sorted duplicate leaves, level
  parents, six checkpoint calls, pure finish. Exact accepted count187+Nparents;
  bare dV count72+Nparents. Annotated experiment has two complete passes.
- Checkpoint source public bytes are ASF8 width1880; model uses semantic
  public width1427/1455. Checked physical_ne_semantic proves the address
  separation under its explicit physical-width/actual-parser conditions.
- Twelve local top facts compile and pass standard-axiom audits. No actual
  source-to-model accepted log law or numerical source bound is claimed.

Recommend B: exact-source frozen3 with separate physical/semantic public carriers,
retaining existing sampler order. Both source refinement and new-model security
composition still required. A/C estimates, explicit losses and caveats are in
that document. No owner adoption implied.

9/40 Lean,0/0 Kani. Four accepted compiles (004/006/008/009), five excluded
elaboration failures. Final009: exit0,1.775738183s,5183240KiB,swap0;
source revision0c706a021e plus exact new audit source snapshot. All twelve
axiom lines standard only. Max all-attempt RSS5209472KiB,swap0. Every run used
6G/8G/swap0/tasks64,-M7000; no timeout, memory kill or cap raise. No package
replay. Full per-attempt fields in LogA_attempts.jsonl and attempt directories.
125 reused source hashes match SInt2; inherited object provenance reused.
No new build infrastructure. No shipped/harness/ELF changes; inherited three
pins are recorded in stage0 and decision document, not rebuilt.

Ledger assumptions removed NONE; trust boundaries retained; S2/100-bit target
not yet established. Next: owner-scoped frozen3 checkpoint-carrier prototype
and same-native-pair complete-verifier join, then probability/extractor closure.
Raw failed stdout is preserved verbatim (including one trailing-whitespace line).
