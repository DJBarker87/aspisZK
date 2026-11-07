"""Read-only receipt review and local report; launches no proof or host command."""
from pathlib import Path
from collections import Counter
import hashlib,json,lzma,re

E=Path(__file__).resolve().parent
read=lambda p:json.loads((E/p).read_text())
H=lambda b:hashlib.sha256(b).hexdigest()
standard={'propext','Classical.choice','Quot.sound'}
receipts={}
for prefix,count in [('K',40),('L',140)]:
 for n in range(1,count+1):
  a=f'NMC_{prefix}{n:03}'
  r=read(a+'/receipt.json');ad=read(a+'-admission.json')
  assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
  assert str(r['swaps'])=='0',a
  receipts[a]=r
assert len(receipts)==180
root_manifest=read('NMC_AUDIT_ROOTS.json');expected=root_manifest['roots'];assert len(expected)==len(set(expected))
results=[];groups=[]
for n in range(30):
 x=read(f'NMC_audit/proof{n}/proof{n}.json')
 assert x['exit_status'] in [0,1]
 assert receipts[f'NMC_L{110+n:03}']['exit_status']==x['exit_status']
 groups.append(dict(target=x['target'],exit=x['exit_status'],roots=len(x['results'])))
 results.extend(x['results'])
seen=[x['root']for x in results]
assert len(seen)==len(set(seen))
missing=sorted(set(expected)-set(seen));unexpected=sorted(set(seen)-set(expected))
nonstandard=[x for x in results if not set(x['walked_axioms'])<=standard]
disagreements=[x for x in results if not x['equal']]
known={'NHC_DecodeModel.decoder_error','AspisR1.NKR_ScheduleExt.transition'}
unknown=[x for x in disagreements if x['root']not in known]
assert not missing and not unexpected and not nonstandard and not unknown
assert {x['root']for x in disagreements}==known
group_sets=[set(g)for g in root_manifest['groups']]
assert all(x['exit']==int(any(not r['equal']for r in results if r['root']in group_sets[int(x['target'][5:])]))for x in groups)
fixtures=read('NMC_audit/fixtures/fixtures.json');assert fixtures['exit_status']==0 and len(fixtures['results'])==8
assert all(x['equal']for x in fixtures['results'])
assert sum(bool(x['walked_axioms'])for x in fixtures['results'])==4
planted={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx']}
assert all(x['walked_axioms']==planted.get(x['root'],[])for x in fixtures['results'])
scan=read('NMC_audit/scan/scan.json');assert scan['exit_status']==0
scanlog=(E/'NMC_audit/scan/scan.log').read_text();assert 'NFN_SCAN_ZERO_DANGLING'in scanlog
assert receipts['NMC_L103']['exit_status']==0
assert receipts['NMC_L140']['exit_status']==0
preflight=read('NMC_PREFLIGHT.json');assert preflight['status']=='PASS_FINAL_PREFLIGHT'
prior=read('NMC_PREDECESSOR_COMPARISON.json');assert all(x['status']=='PASS'for x in prior.values())
export=read('NMC_EXPORT.json')
closure=json.loads(lzma.decompress((E/'NMC_CLOSURE_PINS.json.xz').read_bytes()))
assert H(lzma.decompress((E/'NMC_CLOSURE_PINS.json.xz').read_bytes()))==(E/'NMC_CLOSURE_PINS.json.sha256').read_text().strip()
# Current own proof modules must have a successful, byte-identical source receipt.
modules=[]
for p in sorted((E/'NMC_generated').glob('*.lean')):
 if p.stem.startswith('NMC_Inspect')or p.stem in ['NMC_COMBINED_IMPORT','NMC_Driver','NMC_ProofDriver','NMC_WALKER']:continue
 candidates=[]
 for a,r in receipts.items():
  q=E/a/'sources/NMC_generated'/p.name
  if a.startswith('NMC_L')and r['exit_status']==0 and q.exists()and H(q.read_bytes())==H(p.read_bytes()):candidates.append(a)
 assert candidates,p
 a=sorted(candidates)[-1];log=(E/a/'stdout.log').read_text()
 ax=[l for l in log.splitlines()if 'depends on axioms:'in l or 'does not depend on any axioms'in l]
 if re.search(r'^\s*(?:private\s+)?theorem\s',p.read_text(),re.M):assert ax,p
 for line in ax:
  if 'depends on axioms:'in line:
   names=set(re.search(r'axioms: \[(.*?)\]',line)[1].split(', '))
   assert names<=standard,(p,line)
 modules.append(dict(module=p.stem,attempt=a,sha256=H(p.read_bytes()),printed_axioms=ax))
native=read('NMC_NATIVE_REVIEW.json')
assert native['paired_windows']==17 and len(native['timeouts'])==5 and native['full_segments_closed']==[]
assert read('NMC_CLOSED.json')['rows']==[]
assert read('NMC_LEDGER_DELTA.json')['changed_rows']==[]
def totals(prefix):
 rows=[r for a,r in receipts.items()if a.startswith('NMC_'+prefix)]
 return dict(attempts=len(rows),kinds=dict(Counter(r['kind']for r in rows)),exit_status_counts=dict(Counter(str(r['exit_status'])for r in rows)),wall_seconds=sum(r['wall_seconds']for r in rows),peak_rss_kib=max(int(r['peak_rss_kib'])for r in rows),swaps=0)
report=dict(status='PASS_SUPPORT_GATE',target_not_yet_established=True,row='TX1:136',row_status='OPEN',native_root=None,full_parameterized_fold=None,new_closed_rows=0,headline='AspisR1.RPx_Deployed.deployed',combined_target='NMC_COMBINED_IMPORT',combined_exit=0,combined_campaigns=1,raw_groups=groups,expected_roots=len(expected),observed_roots=len(seen),missing_roots=missing,unexpected_roots=unexpected,nonstandard=nonstandard,collector_disagreements=disagreements,unknown_collector_disagreements=unknown,raw_standard_complete=True,fixtures_exit=0,fixture_controls=8,scan_exit=0,scan_defects=0,loaded_modules=closure['modules'],pins_pass=True,predecessor_comparison=prior,final_pin_exit=0,final_preflight=preflight,export_path=export['export'],export_files=len(export['files']),export_bytes=export['bytes'],budget=dict(kani=totals('K'),lean_support=totals('L'),extraction=0),all_submitted_admissions_pass=True,paired_partial_windows=17,native_timeouts=native['timeouts'],unpaired_positive=['NMC_K038'],full_segments_closed=[],native_process_findings=native['process_findings'],trust_changes=[],frozen_verifier='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_pool='b936275465',release_pool_elf='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc',own_checked_modules=modules,limitations=['No full native parent segment contract, native fold, full ledger RowSpec-parameterized fold or row root.','Raw collector disagreements are retained, with the complete standard-only raw dependency set authoritative.','Partial native windows do not establish the stronger full-G contract goals.','No ELF rebuilt: frozen shipped files were unchanged; pinned historical artifacts are not fresh reproduction claims.'])
(E/'NMC_AUDIT.json').write_text(json.dumps(report,indent=2)+'\n')
plan=read('NMC_AUDIT_PLAN.json');plan['status']='COMPLETED_SUPPORT_ONLY';(E/'NMC_AUDIT_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
(E/'NMC_HANDOFF.md').write_text(f'''# NMC TX1:136 handoff

Target not yet established. TX1:136 remains OPEN. No full native parent segment, native fold, full ledger RowSpec-parameterized fold or row root is supplied. No new CLOSED row or trust item; ledger23 remains580 CLOSED /0 QUALIFIED /19 OPEN. See NMC_CLOSED.json, NMC_LEDGER_DELTA.json and the35-cut NMC_SEGMENTS.md/NMC_CUT_TABLE.json.

## Established support

ONE ReviewedTranscription records NLI_Source.finishSourceEquality over frozen r1_semantic.rs:232-308 plus NLU's35 occurrence schemas (NMC_Transcription.source, L002). NLI's weaker RowSpec is not used as the ledger obligation. Current69 source modules have successful exact-source/dependency receipts. All printed top theorem axioms are standard, and the raw combined gate below checks their transitive dependencies.

NMC_Claims.installed (L069) attaches CLOSED129 to the same live owner/full payload/heap. NMC_Terminal.actual_arguments (L097) derives both canonical arrays and Actual256 full-Result installation at the stored actual source arguments. NMC_Records.decode25/decode26/circle0/circle1 (L102) derive147/142 domains at the actual parsed record and current transcript slots. Complete23-slot source frames, full record projection reassembly, arbitrary raw-region initializedness and Claims-region frames are proved. NMC_Partial.advance (L099) supplies the partial-array prefix/frame step; NMC_RootStages abort-frontier law (L100) preserves the last entered rootTry/unwrap state; emitted QM31 comparison is checked (L101). Exact theorem names, statements, source hashes, print output and focused receipts are retained in NMC_AUDIT.json and NMC_generated/.

These are source/model support and conditional installations, not proof of the compiled parent state chain. NMC_LocalWindows/NMC_Cut_* contain stronger full-effect segment GOALS plus forward support; the partial native assertions do not discharge them. NMC_FOLD.md records this boundary. The archived unattempted NMC_PartialFill draft has no credit.

Native:40 attempts,17 paired partial windows,5 retired timeouts (K001/K002/K021/K039/K040), and unpaired positive K038. No timed-out attempt receives credit. K040 inverted the assertion on K039's same full-entry footprint after K039 timed out; this did not isolate the shape and is recorded as a process finding, not as a valid replacement or failing control. Exact KMX mitigation and matched failing controls are checked in NMC_NATIVE_REVIEW.json; scratch Cargo.lock and the resolved frozen graph were checked before/after EVERY run, offline and with deployed features. Harnesses are committed only as NMC_HARNESSES.patch with SHA, snapshots and receipts. No writable-static or Option<fn>-dependent verdict, field multiplication, SHA unwinding, proof_for_contract or stub_verified credit is claimed.

## Validation and retained assumptions

One support campaign: NMC_COMBINED_IMPORT (L103) imports ledger23 NLS plus NLU/NLI/NLH and the current own modules, with AspisR1.RPx_Deployed.deployed. Eight fidelity controls pass (L108); NFX loaded scan exits0 with zero dangling references (L109). Thirty raw ax2 groups (L110-L139) cover all{len(expected)} roots exactly once, standard axioms only. The two inherited collector underreports, NHC_DecodeModel.decoder_error and AspisR1.NKR_ScheduleExt.transition, remain visible; the raw dependency sets are authoritative under (ab')/(ax2). No unresolved or nonstandard dependency is hidden. NMC_AUDIT.json is support-gate evidence, not row credit.

All180 submitted admissions were exit0 and allowed:true. Usage40/40 Kani,140/140 Lean-support scopes,0 extraction. The support count includes compiler, audit, link, seed and patch/preflight scopes; kind counts are explicit in NMC_AUDIT.json. Each receipt records target/command, exit, wall time, RSS, zero swap, scope limits, source revision/hashes and printed axioms or its non-proof category. Caps remain6G high/8G max/swap0/tasks64, Lean-M7000; one scope at a time. No cap/timeout increase or repeated unchanged full regression. L140 pins the loaded Aeneas/library objects, verifies unchanged copied seeds and predecessors, and exports{len(export['files'])} own files ({export['bytes']} bytes) to {export['export']}. Own cache/target/TMPDIR are retained. Exact cleanup of dead solver files is in NMC_SOLVER_CLEANUP.json.

Discharged locally: the source-domain/provenance/frame/abort obligations named above. Retained: adopted headline hypotheses, existing runtime/allocator/arithmetic child packet assumptions on their existing domains, and the P6/tool trust interpretation. Added or changed assumptions: none. No child success/result/endpoint, arbitrary Ops/Run dictionary or physical/provenance predicate is admitted as a row-root premise. NMC_HYPOTHESES.json and NMC_CALLER_CLAUSES.json record the permitted inventory and the three own-input clauses for caller137. NMC_NLZ_CHECK.json records the read-only research check; no NMC root exists for an implication claim.

Frozen verifier/crates/program r1/Cargo.lock:4bb3b3f51e16b4525f1d10336e2b0bcbbd775387; Pool:b936275465; Pool ELF:e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc. Parameters/wire format are pinned by the frozen source manifests; deployed features are recorded per crate on every native run. Tool and resolved object hashes are in NMC_TOOL_PINS.json/NMC_CLOSURE_PINS.json.xz. Shipped files remain unchanged. No ELF rebuild was triggered or fresh ELF reproduction claimed. The100-bit per-attempt target, privacy and two-transaction design are unchanged and are not established by this support work.

## Remaining deliverable

Both scoped allowances are exhausted; stopping is not caused by Kani exhaustion alone. NMC_REMAINING.md lists each occurrence's native AND Lean-only obligations. Next: split the retired terminal-entry shape into actual argument windows with matched controls; bind ONE original input, partial destination, Reservation/allocator, live owner/full heap and full Result through each source-ordered segment; prove all strong-G/source associations and the lifecycle/abort-preserving fold against the FULL ledger136 obligation. Do not replace these by the partial windows, NLI's weaker value interface or accepted-child hypotheses. Row credit waits for the next ledger gate. No push, sibling worktree write, key cleanup or shipped-source edit occurred.
''')
(E/'NMC_REMAINING.md').write_text((E/'NMC_REMAINING.md').read_text().replace('This is not a stop on Kani exhaustion alone: Lean-only source/domain/frame work and the required gates continue through the remaining allowance. Final actual usage belongs to NMC_AUDIT.json.','Both allowances are now exhausted:40/40 native and140/140 Lean-support scopes,0 extraction. Lean-only source/domain/frame proofs continued after native exhaustion, then the single required combined support gate completed. Exact categories and metrics are in NMC_AUDIT.json. There is no early stop below80 percent; remaining Lean-only obligations are explicitly retained below.'))
print(json.dumps({k:report[k]for k in ['status','row_status','expected_roots','observed_roots','loaded_modules','new_closed_rows','budget']}))
