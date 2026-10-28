# Batch3c D323 — stopped on a second native fixture disagreement

Exact worktree `/Users/dominic/ZK/.worktrees/pv-l3`, branch `codex/pv-batch3-20261027`, entry73a25b0b8bab8250accdbaac79d397fdf410a8ac. No merge/push. Prior handoff preserved in RESUME-HANDOFF-before-batch3c.md.

## Rejected repair and mandatory stop

**Do not adopt/merge source1be0505afc.** The authorized repair was to restore21 PRIVATE path steps, retaining20 append steps and127 total links. I mistakenly added level20 to BOTH private-path and append expansions. The new schedule has129 links (11 initial +63 private +7 value/conservation +2 input +4 output +42 append), so the unchanged127-link check rejects it. The frozen source has only40 append links (`pair_tree_hiding.rs:224`, `0..20usize`). This is another worker rewrite error, not a ROWS5 counterexample. The earlier handoff's omitted three private links was correct; the second append addition was my incorrect inference.

Optimized `batch3c-split-bench-01` compiles then exits101 at main.rs16 with `unwrap()` on Err(Shape), before any timing sample. This invokes the standing fixture-disagreement stop. No subsequent source correction, extraction, Lean compile, fixture-byte execution, cost projection or audit ran. The129-link diagnosis is static source arithmetic, not an additional native test. The next repair is to remove only `legacy_append_step(links,20)` while retaining `legacy_path_step(links,20)` and the127-link check, under renewed authorization.

Both rejected binaries retained on host: old `bin/batch3b-split-counterexample` (source0b048ee98d, SHA256 fe278db2829e72ecbbbc61702042427c6152d9f9341702965c8aa457bfad54a3), new `bin/batch3c-split-counterexample` (source1be0505afc, SHA256 f7e59b38d874885a680737e4e84e16c1bc2d5a7235e0b502dda57f9f2fe6884b). Never merge either rejected source.

## Gates and receipts

All three repaired-candidate ELFs match the frozen pins:

- default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4
- devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299
- Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548

| Target label | Exit | Wall s | Peak RSS KiB | Swap |
|---|---:|---:|---:|---:|
|batch3c-repair-elf-01-default|0|49.931|686560|0|
|batch3c-repair-elf-01-devnet|0|2.576|208088|0|
|batch3c-repair-elf-01-pool|0|30.992|681868|0|
|batch3c-split-bench-01|101|39.694|568216|0|

All receipts source1be0505afc; #print axioms N/A (Rust/SBF only). Full commands, admission/barrier outputs, systemd6G/8G/swap0/Tasks64 caps, compiler logs, time and cgroup peaks are retained in receipts/ and batch3c-receipt-index.json. No refusal or overlapping scope occurred. Native work used release optimization and four pinned CPUs. Last valid Rust/cost freeze remainsc97270adc2, worst+1.906124819123782%. This rejected repair has no valid cost projection; the cost-triggered fallback was not reached. crates/ was not restored to c97270adc2.

## Proof status and budget

This resume used0 Lean attempts and0 Kani;85 Lean attempts remain. Next unused ID37916;37916–37996 focused and37997–37999 audit remain unused by this resume. No external/project object was imported or compiled, so no h4/h5/h5' source authority decision was exercised. No shared source/object writes. Existing proof receipts remain historical evidence for their recorded inputs.

Rows closed0. Every ExternalFuns residual in V217,V220,V228,V229,V230,V239,V241,V243,V244,V245 remains P/OPEN before and after. No premise removed/added/weakened; T unchanged (entropy_law,entropy_kernel,observation). Native/emission222 comparison,222 universal original/copy and row bridge,134 native association/installation and117/121 universal equalities remain unattempted. D234/V403, deployment/E1/E2/RunJoin and L1/L2/L3 remain open. Target not yet established.

No further extraction rewrite of132/133/224/226/227/228 was attempted. Their blockers remain exactly as in the prior handoff:132/133/228 context joins,224 escaping Vec/slice references,226 SymbolicToPureAbs projection failure,227 escaping reference after Drop removal.

## Retention

No keys or nonce ledgers deleted. Three new artifact keypairs are0600; previous retained keys remain. No own scopes remain. The new counterexample binary was copied before removing only the job-private Rust target cache. sbf-target was retained because the conservative scanner found a nonce-named JSON; no shared path deleted. See batch3c-cleanup.json and batch3c-source-verification.json.
