# NMH extraction provenance handoff

**Target not yet established.** Branch codex/cx-emission-repro-20261107; local commits only, no push. This packet investigates NKT-F2, without a new row proof, ledger edit, trust change or shipped-source change.

11/30 serial extraction scopes completed. Verdicts for all 336 requested blobs: {'NOT_REPRODUCED': 318, 'DIFFERS': 17, 'REPRODUCED': 1}. Tool charges: {'Charon': 11, 'Aeneas': 9, 'Lean': 0, 'Kani': 0}; limits Charon30/Aeneas30/Lean10/Kani0. See NMH_PROVENANCE.json for each blob's committed/reproduced hashes, run, verdict, reason and affected CLOSED rows. NMH_PLAN.json records packet partitions and one explicit configuration per run. NMH_REMAINING.md records every unresolved member.

Frozen crates, verifier program and Cargo.lock: 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. Pool: b936275465 (full git revision and per-file git/SHA pins in NMH_STAGING_MANIFEST.json). NMH_NHR_stage.py is unchanged NHR_stage.py; NMH_extract.py supplies archived options or explicitly labelled diagnostic selectors through its API. All original source/lock/graph/tool checks remain. NMH_CLIENT_CHANGES.md records the owned controller adaptations. No shared launcher, reservation, shim, workspace or sibling worktree changed.

Every launched scope has reservation exit0 and allowed:true, a >=40GB free-disk check, and 6G high/8G max/swap0/64-task limits. One scope at a time; optimized release Rust; timeout180 unchanged. NMH_ATTEMPTS.jsonl, NMH_TOOL_ATTEMPTS.jsonl and per-run receipts record exact commands, pins, source revision, exits, wall, RSS, swaps and cgroup peaks. No failed/timed-out shape is rerun unchanged. Own host writes remain limited to the assigned workspace and below30GB.

All 1,081 distinct ledger24 CLOSED roots have archived reachability lists; NMH_ROW_IMPACT.json.xz pins each list and intersects fully qualified declarations. Historical aliases defining the same constant remain conservative source-to-object candidates. This is not a replacement for NKT's missing selected-source/object mapping. The batch_tree family is cross-referenced to NKT-F1/(bc). The lead decides row consequences; no row or trust item is reopened or edited here.

No new theorem or Lean compile: #print axioms is not applicable. Raw Aeneas external templates are uncompiled evidence, never new trusted axioms. No hypothesis, runtime/cryptographic assumption, metric, carrier, privacy requirement or two-transaction requirement is added, discharged or changed. Headline remains AspisR1.RPx_Deployed.deployed with L154 parameter and narrowed D188.

No shipped-file or cfg(kani) change, so no ELF rebuild trigger. Inherited only: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548. No key/wallet operation occurred.

Validation: NMH_tests.py parser/comparator controls; NMH_validate.py checks full336 coverage, admitted/capped receipts, retained output hashes, tool budgets, unchanged ledger/shipped inputs and20MB hygiene. Its result is PASS_WITH_PROVENANCE_GAPS, never a universal fidelity or100-bit security pass.
