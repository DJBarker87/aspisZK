# NML archive extraction provenance handoff

**Target not yet established.** Branch codex/cx-emission-repro2-20261107. Local commits only; no push.

Scope: archived-input provenance for 336 NMH blobs, including the 195 reference-crate and 81 configuration gaps; semantic classification of 17 byte differences. No Kani, row proof, ledger edit, trust edit or shipped-source edit.

Current verdicts: {'NOT_REPRODUCED': 317, 'REPRODUCED_FROM_ARCHIVE': 17, 'DIFFERS_SEMANTIC': 2}. Conservative remaining CLOSED-row impact: 561/581, with rootless TX1:059/TX2:040 still unassessed. This is the unchanged NMH lexical declaration/root-list method, not a selected-source/object certification and not a row reopening.

30 archived source groups with candidate configurations; 40 distinct planned Charon configurations. One historical --locked input lacks its archived lock, as explicitly recorded. Remaining configurations run serially in explicit batches of at most ten within one admitted capped scope, preserving all per-configuration NHR checks and timing receipts. Completed extraction scopes: 40/40. Tool charges: {'Charon': 40, 'Aeneas': 39, 'Lean': 1, 'Kani': 0}; limits 40 Charon / 40 Aeneas / 20 Lean / 0 Kani. All remaining members and classification obligations are listed in NML_REMAINING.md. Extraction budget exhausted; no failed or timed-out shape rerun unchanged.

NML_INPUT_MAP.json records producing receipts, Git blobs, exact embedded-LLBC source hashes, manifests and configurations. NML_PLAN.json records the grouped commands. NML_PROVENANCE.json covers every blob; NML_DEFINITION_COMPARISONS.json.xz retains exact declaration segment comparisons. Only whole-byte identity or NHR_parameterize.py discriminant metadata removal is accepted. Namespace/import/parameter changes are never normalized away.

The unchanged pinned NHR_stage.py performs frozen source/graph/lock/tool checks. Owned controllers independently check archived source/manifests. Host workspace /home/dombarker/project-offloads/codex-cx-emission-repro2-20261110 only; one scope at a time. Every submitted scope requires Stream A count <2, reservation exit0 AND allowed:true, >=40 GB free, and exact caps 6G high / 8G max / swap0 / 64 tasks. Receipts retain command, tool pins, input hashes, source revision, exit, wall, peak RSS, swap and axioms status. Current sum of per-configuration/Lean wall 61.048s; maximum process RSS 2602496KiB. Batch scope totals and per-configuration totals are separate receipts and are never added twice. Refusals are recorded waits, not launches.

Frozen crates/verifier/lock 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool b936275465. Correct inherited Pool ELF: e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc; default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299. These are inherited artifact pins, not rebuilt here. No shipped change triggers a rebuild. No wallet/key operation occurred.

The original 17 byte differences are classified as 2 SEMANTIC, 0 NON-SEMANTIC and 15 UNCLASSIFIED. NML_L001 compiled the exact paired scalar bodies; all five new top theorems print only [propext, Classical.choice, Quot.sound]. The U32-overflow witnesses lie outside canonical M31 and prove no canonical-domain caller defect.

No assumption is added, discharged or changed. Headline remains AspisR1.RPx_Deployed.deployed; L154 is a statement parameter; D188 remains narrowed. Uncompiled external templates are evidence only and never trusted new axioms. Lean checks, if successful, classify exact compared bodies only and do not close a native caller row.

Validation: NML_tests.py rejects namespace/body/addition/partial-match mutants; NML_validate.py audits coverage, budgets, source hashes, admitted/capped receipts and 20 MB hygiene. The validation status explicitly includes the excluded admission finding; it is never a universal extraction or 100-bit security pass.

Procedural finding: E001 is excluded from all provenance credit because its restarted waiter rechecked after 15.095 seconds rather than 180. Its tool charges remain; resource admission/caps passed. NML_ADMISSION_FINDING.json and NML_FINDINGS.md retain the evidence. The client now preserves refusal deadlines across restarts. No unchanged rerun.

Formal comparison receipt: target NML_DiffArithmetic.lean; exit 0; wall 3.1486780210398138s; peak RSS 2602496KiB; swaps 0; source revision 1a81898c693126c742df88bf7a5d1c6ad2b9a9fc; full five #print axioms lines in NML_L001/receipt.json.

Final host audit: no active owned process, no frozen source/lock drift. Owned bytes 267310129 before cleanup, 263602372 after removing only owned Cargo/proof-object scratch; free disk 134792630272 bytes. The prescribed retained prepared cache was untouched. Artifact hashes and exact deleted-output sizes are in NML_HOST_POSTCHECK.json.
