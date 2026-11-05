from pathlib import Path
import json,re,hashlib,lzma,collections,subprocess
E=Path(__file__).resolve().parent;J=lambda n:json.loads((E/n).read_text())
audit=J('NHO_AUDIT.json');scan=J('NHO_SCAN.json');metrics=J('NHO_METRICS.json');seed=json.loads(lzma.decompress((E/'NHO_CACHE_IMPORTS.json.xz').read_bytes()));export=J('NHO_EXPORT.json')
# Quote full exact kernel statements from the one final print target.
source=(E/'NHO_PLAN_STATEMENTS.lean').read_text();log=(E/'NHO_L040/stdout.log').read_text();quotes=[];lines=['# Exact kernel-loaded plan and headline statements','','No native-observation hypothesis is supplied by these quotations.','']
for name in re.findall(r'^#check @([\w.]+)',source,re.M):
 match=re.search(r'^@?'+re.escape(name)+r'(?:\.\{[^}]*\})? :',log,re.M);assert match,name
 ax=re.search("'"+re.escape(name)+"' (?:depends on axioms:\\s*\\[[^\\]]*\\]|does not depend on any axioms)",log[match.start():]);assert ax,name
 quote=log[match.start():match.start()+ax.end()];quotes.append(dict(name=name,attempt='NHO_L040',quote_sha256=hashlib.sha256(quote.encode()).hexdigest(),axiom_line=ax[0]));lines+=['## '+name,'','```lean',quote,'```','']
(E/'NHO_STATEMENTS.md').write_text('\n'.join(lines));(E/'NHO_STATEMENT_QUOTES.json').write_text(json.dumps(quotes,indent=1)+'\n');assert len(quotes)==5
p=E/'NHO_STATEMENT.md';s=p.read_text().replace('Full kernel statements and fresh axiom output are requested in NHO_L040.','Full kernel statements and fresh axiom output are quoted in NHO_STATEMENTS.md from NHO_L040 (exit0).')
dis=audit['collect_axioms_disagreements'];s+='\n## Completed third all-slices composition test\n\nNHO_L004 combines every selected CLOSED forest, canonical Pool, (ah) prepared_claim, NGP/NGR/NGS and RPx_Deployed.deployed. All'+str(audit['root_count'])+' unique selected roots are raw-walked with standard axioms only. The eight planted/mutation fixtures pass in the SAME unchanged compiled proof binary. Full walker byte equality, compiled object pins and driver diffs are retained. NHO_L010 full scanner exits0 over'+str(scan['modules'])+' modules,'+str(scan['declarations'])+' declarations and'+str(scan['edges'])+' references, with zero dangling references, incompatible owners and import mismatches;'+str(scan['compatible_cached_replicas'])+' compatible cached replicas are disclosed. NHO_CONFLICTS.json records no owner conflict and no qualified row.\n'
if dis:s+='\nRaw/summary discrepancy retained under C3-BIN(ab\')(3): '+', '.join(d['root']+' in '+d['attempt']for d in dis)+'. The raw set is {propext, Classical.choice, Quot.sound}; collectAxioms reports none. The affected audit exit1 remains recorded; it is NOT relabelled exit0. Raw standard-only authority is used exactly as admitted by (ab\'), without a new axiom or forest patch.\n'
s+='\nAll40/40 slots are used: '+str(metrics['by_kind'])+'. No Kani, extraction, new theorem, timeout, memory kill or cap increase. This is focused cached composition, not L187 or a deployed security theorem.\n';p.write_text(s)
# Scope policy corroboration: no own populated scope at admission.
admissions=[]
for p in E.glob('NHO_L[0-9][0-9][0-9]-admission.json'):
 x=J(p.name);assert x['exit']==0 and x['reservation']['allowed']is True
 own=[q for q in x['reservation'].get('populated_scopes',[])if any('/codex-cx-ledger10-20261106/'in c or 'S2W_run_host.py NHO_'in c for c in q.get('processes',[]))];assert not own,p.name
 admissions.append(dict(receipt=p.name,exit=0,allowed=True,own_populated_scopes=own,bounded_reserved_bytes=x['reservation'].get('bounded_reserved_bytes')))
(E/'NHO_SCOPE_ADMISSION_AUDIT.json').write_text(json.dumps(dict(status='PASS',one_scope_at_a_time=True,attempt_admissions=admissions),indent=1)+'\n')
branch=subprocess.check_output(['git','branch','--show-current'],text=True).strip();commits=subprocess.check_output(['git','log','--oneline','-3'],text=True).strip()
text=f'''# Ledger refresh10 final handoff

**335/599 CLOSED,0 QUALIFIED,264 OPEN. Target not yet established.**
Branch {branch}. No push, merge, shipped-source change, new theorem, Kani, extraction or wallet/key operation.

## Exact result

NHO_LEDGER.json.xz (uncompressed SHA retained) preserves the immutable NGZ/NGB599-row source graph. All eight delta/Pool validators reproduce unchanged with extra checks only; NHO_VALIDATOR_PROVENANCE.json pins their bytes, NHO_TESTS.json rejects evidence mutations. 34 claimed occurrences minus NGX TX1:151/152 already CLOSED yield32 new occurrences,335 total; the approximate325 estimate differs by10. NHO_COUNT_RECONCILIATION.json records exact rows and all overlaps. NGW's old scanner exit1 alone earns no credit; NHE_L001 rerun exit0 is checked.

TX1:182 CLOSED/171 OPEN; TX2:153/93. S97/97,Q159/161,D83/345; four S/Q overlaps count once globally. TOOL-BOUNDARY TX1:036/040/041/043/044 remain OPEN. CM31::inv_with and QM31::neg remain OPEN. Pool supported_loader is CLOSED outside599; Pool B/D remain OPEN. No row is promoted by support-only work or a running sibling's WIP.

## Third all-slices composition test

NHO_L004 imports canonical NGK plus every newly selected forest, Pool, (ah) prepared_claim, NGP/NGR/NGS and AspisR1.RPx_Deployed.deployed. NHO_AUDIT.json raw-walks{audit['root_count']} unique roots with standard axioms only. The same compiled proof binary passes all eight planted/mutation fixtures. Walker bytes equal NEP_WALKER and compiled conformance pins match NGK; full driver diffs are committed.

NHO_SCAN.json: exit0,{scan['modules']} modules,{scan['declarations']} declarations,{scan['edges']} references; zero dangling references, incompatible owners or import mismatches. {scan['compatible_cached_replicas']} compatible cached replicas are disclosed. No owner conflict or qualified row; no forest/declaration renamed, patched or weakened.

Raw/summary disagreements: {str(dis)}. These retain the actual exit1 and are classified under binding(ab')(3), raw standard-only authoritative. Failed imports L001/L002/L003 were missing cached NFG dependencies, restored read-only with exact pins/provenance; no timeout or memory failure. Own sandbox/seed/archiver repairs and excluded runs are retained in NHO_PREFLIGHT_FIXES.json, NHO_DEPENDENCY_CHANGES.json and source versions. No validation predicate changed.

## Honest statement and retained assumptions

NHO_STATEMENT.md records three of ten plan items proved conditionally: AspisR1.NGR_HISTORY.saved_to_loaded; AspisR1.NGS_CARRIERS.same_inputs_or_collision; ORACLE.partial_and_returning implemented by AspisR1.NGP_OracleTransport.prefix_of_native and exact_of_returns. L004 and L040 print all four names and the headline with [propext, Classical.choice, Quot.sound]. NHO_STATEMENTS.md quotes complete fresh kernel statements. The missing native-observation hypotheses are not supplied.

NHO_SHORTEST_PATHS.md recomputes unchanged OPEN entry-to-accept paths and lists each spine owner/last obligation: NHD/NGL adapter, NHF/NHL prepare/TX1, NHE/NHI tail, NHC Pool. NHO_READONLY_PROVENANCE.json pins the NHL branch snapshot; no live sibling worktree was read or edited. NHO_REMAINING.md retains exact remaining production Pool obligations; old NGG item10 retargeting is complete, while B/D remain OPEN.

Ruling(aj)'s owner points remain: confirm L159 physical reporting boundary (recommended same-game Pool B/D settlement route continues); any uncovered adaptive reorder requires owner choice of coupling versus frozen3 change. Partial terminal policy remains failure/divergence, ideal suffix and pointwise domination. L187 cold coherent release replay and L188 final trust/axiom/native/source-to-ELF audit remain OPEN.

No trust removed. P6/D188 option-A native semantic transport and reviewed polynomial fold are retained RECLASSIFICATION. RuntimePersistence,digest/H,SDK/std/allocator/ABI/compiler/Aeneas/source-to-ELF and cryptographic assumptions remain. ReviewedTranscription-prepared_claim is ADDED-LEAD (ah), used by TX1:193; RuntimeClockSlotBinding is ADDED-LEAD, same-instruction bankSlot only. RuntimeReturnData(nonempty1..1024,ASR8=792) and RuntimeMemcmp are ACCEPTED. RuntimeCpiReadonlyEntry7 is ADDED-PENDING-LEAD and UNUSED. Direct use is separated from retained realization in NHO_TRUST_USED.json. L154 is a statement parameter; digest/error op43/op44.100-bit PER-ATTEMPT soundness, privacy and two transactions are unchanged.

Crates/programs remain byte-identical to frozen4bb3b3f51e16b4525f1d10336e2b0bcbbd775387. No ELF rebuild trigger. INHERITED ONLY, not rebuilt/rehashed: default f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4; devnet63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299; Pool121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548.

## Resources, restoration and next deliverable

40/40 slots:{metrics['by_kind']}; {metrics['successful']} successful; retained failures{metrics['failures']}. Wall sum{metrics['scope_wall_sum_seconds']:.6f}s; peak RSS{metrics['peak_rss_kib']}KiB; swaps0. Exact targets/argv/revision/source/direct/Aeneas dependency pins/exit/wall/RSS/swap/axioms are in NHO_ATTEMPTS.jsonl and40 receipts. Every admission exit0 AND allowed:true; one scope at a time; MemoryHigh6G/MemoryMax8G/MemorySwapMax0/TasksMax64, Lean-M7000, optimized links. No timeout, memory kill, cap raise or unchanged resource-failure retry.

Initial seed{seed['paths']} paths,{seed['logical_bytes']} logical bytes,{seed['external_copy_bytes']} external copy bytes; supplements retain hashes separately. Owned cache /home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NHO_flat is RETAINED. Restore its NHO_exports_20261106 FIRST, then NHO_flat, coherent SInt2 workspace/objects and pinned Lean4.32. NHO_EXPORT.json retains{len(export['files'])} own objects ({export['bytes']} bytes); NHO_CLOSURE_PINS.json.xz pins every actually resolved module/sidecar including Aeneas. NHO_PACK.json stores repeated large receipt inputs once by SHA; no file over20MB, compiled binary/object/ELF/tarball or __pycache__ is committed. Final artifact/cleanup verification is recorded separately. No predecessor/sibling cache, infrastructure or key was deleted.

Next: close actual D/native writer/preparation/transcript/driver/experiment producers and Pool B/D associations under the adopted plan, then L187/L188. Cached forest coherence is a checkpoint, not deployed soundness. **Target not yet established.**

Local stage commits at report generation:
```
{commits}
```
'''
(E/'NHO_HANDOFF.md').write_text(text);print('report written; exact plan statements',len(quotes))
