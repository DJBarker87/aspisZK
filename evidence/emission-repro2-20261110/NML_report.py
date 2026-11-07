"""Refresh member-by-member handoff without changing ledger or trust records."""
from pathlib import Path
import json,collections,hashlib
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
def main():
 p=load('NML_PROVENANCE.json');plan=load('NML_PLAN.json');im=load('NML_INPUT_MAP.json');cl=load('NML_DIFFS_CLASSIFIED.json');completed={f.parent.name:json.loads(f.read_text()) for pattern in ['NML_[EL][0-9][0-9][0-9]/receipt.json','NML_E[0-9][0-9][0-9]/configuration_receipt.json'] for f in E.glob(pattern)};pending=[r['run'] for r in plan['runs'] if r['run'] not in completed]
 im['blobs']=[dict(blob=h,group=g['group'],mapping_indices=list(range(len(g['mappings']))),archived_package_indices=list(range(len(g['archive_sources']))),source_status=g['status']) for g in im['groups'] for h in g['members']]
 (E/'NML_INPUT_MAP.json').write_text(json.dumps(im,indent=2)+'\n')
 text=f'''# NML remaining obligations

Target not yet established. No ledger or trust edit. Completed extraction scopes: {40-len(pending)}/40; remaining planned scopes: {len(pending)}. Charged tools: {p['budget_used']}; limits Charon 40 / Aeneas 40 / Lean 20 / Kani 0.

'''
 text+=('Work is ongoing; share-gate waits are not tool attempts.\n\n' if pending else 'All planned extraction scopes are terminal. Unused Lean allowance is not spent on renaming nominal carriers or fabricating missing extraction configuration: neither establishes definitional equality. The difference entries below explain each remaining Lean obligation.\n\n')
 text+='''## Member-by-member status

Every non-reproduced member remains a release provenance obligation. The exact group source/configuration candidates are in NML_INPUT_MAP.json; successful byte comparisons and original NMH impacts are in NML_PROVENANCE.json. No partial declaration match is promoted to whole-blob identity.

| Blob | Group | Verdict | Exact remaining obligation |
|---|---|---|---|
'''
 for b in p['blobs']:
  if b['verdict']=='REPRODUCED_FROM_ARCHIVE':continue
  text+=f"| {b['blob']} | {b['group']} | {b['verdict']} | {b['reason'].replace('|','/')} |\n"
 text+='\n## The 17 byte differences\n\n'
 for b in cl['blobs']:text+=f"- `{b['blob']}`: **{b['classification']}**. {b['reason']}\n"
 text+='\n## Budget and boundary accounting\n\n'
 text+='No Kani or row proof is authorized. No new trust row, trust change, source adoption or ELF rebuild. Remaining non-reproduced blobs conservatively reach '+str(p['affected_CLOSED_count'])+' CLOSED rows by NMH lexical-name impact; historical aliases remain conservative, and TX1:059/TX2:040 remain unassessed. A reproduced reference input does not itself prove correspondence to the frozen native function.\n'
 (E/'NML_REMAINING.md').write_text(text)
 totalwall=sum(float(r['wall_seconds']) for r in completed.values());rss=max([int(r['peak_rss_kib']) for r in completed.values()]+[0])
 hand=f'''# NML archive extraction provenance handoff

**Target not yet established.** Branch codex/cx-emission-repro2-20261107. Local commits only; no push.

Scope: archived-input provenance for 336 NMH blobs, including the 195 reference-crate and 81 configuration gaps; semantic classification of 17 byte differences. No Kani, row proof, ledger edit, trust edit or shipped-source edit.

Current verdicts: {p['counts']}. Conservative remaining CLOSED-row impact: {p['affected_CLOSED_count']}/581, with rootless TX1:059/TX2:040 still unassessed. This is the unchanged NMH lexical declaration/root-list method, not a selected-source/object certification and not a row reopening.

30 recovered input groups; 40 distinct planned configurations. Remaining configurations run serially in explicit batches of at most ten within one admitted capped scope, preserving all per-configuration NHR checks and timing receipts. Completed extraction scopes: {40-len(pending)}/40. Tool charges: {p['budget_used']}; limits 40 Charon / 40 Aeneas / 20 Lean / 0 Kani. All remaining members and classification obligations are listed in NML_REMAINING.md. {('Work continues after share admission.' if pending else 'Extraction budget exhausted; no failed or timed-out shape rerun unchanged.')}

NML_INPUT_MAP.json records producing receipts, Git blobs, exact embedded-LLBC source hashes, manifests and configurations. NML_PLAN.json records the grouped commands. NML_PROVENANCE.json covers every blob; NML_DEFINITION_COMPARISONS.json.xz retains exact declaration segment comparisons. Only whole-byte identity or NHR_parameterize.py discriminant metadata removal is accepted. Namespace/import/parameter changes are never normalized away.

The unchanged pinned NHR_stage.py performs frozen source/graph/lock/tool checks. Owned controllers independently check archived source/manifests. Host workspace /home/dombarker/project-offloads/codex-cx-emission-repro2-20261110 only; one scope at a time. Every submitted scope requires Stream A count <2, reservation exit0 AND allowed:true, >=40 GB free, and exact caps 6G high / 8G max / swap0 / 64 tasks. Receipts retain command, tool pins, input hashes, source revision, exit, wall, peak RSS, swap and axioms status. Current sum of per-configuration/Lean wall {totalwall:.3f}s; maximum process RSS {rss}KiB. Batch scope totals and per-configuration totals are separate receipts and are never added twice. Refusals are recorded waits, not launches.

Frozen crates/verifier/lock 4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool b936275465. Correct inherited Pool ELF: e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc; default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet 63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299. These are inherited artifact pins, not rebuilt here. No shipped change triggers a rebuild. No wallet/key operation occurred.

No assumption is added, discharged or changed. Headline remains AspisR1.RPx_Deployed.deployed; L154 is a statement parameter; D188 remains narrowed. Uncompiled external templates are evidence only and never trusted new axioms. Lean checks, if successful, classify exact compared bodies only and do not close a native caller row.

Validation: NML_tests.py rejects namespace/body/addition/partial-match mutants; NML_validate.py audits coverage, budgets, source hashes, admitted/capped receipts and 20 MB hygiene. PASS_WITH_PROVENANCE_GAPS is never a universal extraction or 100-bit security pass.
'''
 if (E/'NML_ADMISSION_FINDING.json').exists():hand+='\nProcedural finding: E001 is excluded from all provenance credit because its restarted waiter rechecked after 15.095 seconds rather than 180. Its tool charges remain; resource admission/caps passed. NML_ADMISSION_FINDING.json and NML_FINDINGS.md retain the evidence. The client now preserves refusal deadlines across restarts. No unchanged rerun.\n'
 (E/'NML_HANDOFF.md').write_text(hand)
 print(json.dumps(dict(completed_extractions=40-len(pending),pending=len(pending),counts=p['counts'])))
if __name__=='__main__':main()
