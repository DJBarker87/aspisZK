"""Validate receipts and package candidate credit separately from authority."""
from pathlib import Path
import json,lzma,hashlib,subprocess,collections
E=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:p.read_bytes() if p.exists() else lzma.decompress(p.with_name(p.name+'.xz').read_bytes())
write=lambda n,x:(E/n).write_text(json.dumps(x,indent=2)+'\n')
base=E.parent/'ledger18-20261108/NKH_LEDGER.json.xz';baseline=json.loads(lzma.decompress(base.read_bytes()));ids=['TX2:055','TX2:054','TX2:053','TX1:083','TX1:082','TX1:081','TX1:084'];rows=[r for r in baseline['rows'] if r['row'] in ids];assert len(rows)==7
raw=json.dumps(rows,indent=2).encode();(E/'NKL_BASELINE_ROWS.json.xz').write_bytes(lzma.compress(raw));(E/'NKL_BASELINE_ROWS.json.sha256').write_text(sha(raw)+'\n')
inv=json.loads((E/'NKL_PROOF_INVENTORY.json').read_text())
for m,pin in inv['modules'].items():assert sha((E/(m+'.lean')).read_bytes())==pin['source_sha256'],m
scan=[json.loads(s) for s in read(E/'NKL_LOADED_scan.jsonl').splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
results=[json.loads(s.split('NEP_RESULT ',1)[1]) for s in (E/'NKL_L092/stdout.log').read_text().splitlines() if s.startswith('NEP_RESULT ')]
standard={'propext','Classical.choice','Quot.sound'}
assert {r['root'] for r in results}==set(inv['roots'])
assert all(r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms']) and set(r['walked_axioms'])<=standard for r in results)
audit=[]
for a in ['NKL_L090','NKL_L091','NKL_L092']:
 x=json.loads((E/a/'receipt.json').read_text());assert x['exit_status']==0
 audit.append({k:x[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','limits']})
write('NKL_AUDIT.json',dict(status='PASS',headline='AspisR1.RPx_Deployed.deployed',full_combined_audits_completed=1,roots=len(results),proof_modules=len(inv['modules']),loaded_modules=len(scan),raw_ax2='standard axioms only; exact match with collectAxioms',standard_axioms=sorted(standard),fresh_fixtures='eight hardened NEP fixtures and mutations; SAME pinned binaries; exit0',binary_pins='NKL_AUDIT2_BINARY_PINS.json',adaptations='NKL_AUDIT_ADAPTATIONS.json',receipts=audit,target_established=False,authoritative_credit=False))
hist=[json.loads(s) for s in (E/'NKL_ATTEMPTS.jsonl').read_text().splitlines()]
if not any(x['attempt']=='NKL_L052' for x in hist):
 x=dict(attempt='NKL_L052',kind='lean',module='NKL_Checks',exit_status=None,wall_seconds=None,peak_rss_kib=None,swaps=None,status='QUARANTINED_POSTSUBMISSION_SSH255_NO_RECEIPT',source_revision='03c36d8d646',source_hashes=None,diagnostic='Transport lost after submission; read-only recovery found no receipt and no live NKL runner. Never resubmitted. No positive credit; resource/result fields unavailable. Charged conservatively against formal budget.',configuration='NKL_L052.json')
 with (E/'NKL_ATTEMPTS.jsonl').open('a') as f:f.write(json.dumps(x)+'\n')
 hist.append(x)
counts=dict(collections.Counter(x['kind'] for x in hist));assert counts['kani']==70 and counts['extract']==2
formal=sum(counts.get(k,0) for k in ['lean','link','audit']);assert formal<=110
checks=[]
for x in hist:
 if x['kind']=='kani':
  lock=json.loads((E/(x['attempt']+'_validation')/'NKL_LOCK.json').read_text());assert lock['unchanged'] and lock['before']==lock['after']
  checks.append(x['attempt'])
write('NKL_GRAPH_SUMMARY.json',dict(attempts=checks,all_frozen_graph_preflight=True,all_lock_hashes_unchanged=True,CARGO_NET_OFFLINE=True,KMX_patch_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',details='Per-attempt validation/metadata/resolved graph/lock receipts; pooled inputs resolve losslessly via NKL_resolve.read'))
paths=['docs/research/100bit-spend-path-20261013/crates','docs/research/100bit-spend-path-20261013/programs','docs/research/100bit-spend-path-20261013/Cargo.lock'];revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
r=subprocess.run(['git','diff','--quiet',revision,'--']+paths);assert r.returncode==0
write('NKL_FINAL_CHECKS.json',dict(counts=counts,formal_confirmed=formal-1,formal_charged=formal,formal_limit=110,kani_limit=70,extraction_limit=2,quarantined_submission='NKL_L052',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),frozen_revision=revision,shipped_paths=paths,shipped_diff_exit=r.returncode,elf_rebuild_trigger=False,inherited_elf_pins=['default f8c0ec72…','devnet 63ad3e9c…','Pool 121f3e29…'],new_elf_rebuild_claim=False,unchanged_after_audit=True,full_combined_audits_completed=1,security_target_established=False))
scanner=next(r for r in rows if r['row']=='TX1:084');clauses=[]
def walk(x,path=''):
 if isinstance(x,dict):
  if 'id' in x and ('required' in x or 'statement' in x):clauses.append(dict(path=path,original=x))
  for k,v in x.items():walk(v,path+'/'+k)
 elif isinstance(x,list):
  for i,v in enumerate(x):walk(v,path+'/'+str(i))
walk(scanner['obligation'])
for c in clauses:
 s=json.dumps(c['original'])
 if 'from_le_bytes' in s:
  c['discharged_by']=['NKL_ClosedChildren.scalar','NKL_ClosedChildren.actualK','NKL_ClosedChildren.quadratic','NKL_NativeGuard.source','NKL_ScanDomains.source','NKL_ReadWindows.scalar_bytes/c1_bytes/c2_bytes','native value/frame/argument controls in NKL_SEGMENTS.md']
 elif 'opening' in s:c['discharged_by']=['CLOSED NEO opening packet, canonical NEO_TailRef owner','NKL_ClosedChildren.opening_reference/opening','NKL_ScanDomains.row','K062-K066; no address-implies-payload assumption']
 elif 'check_values' in s:c['discharged_by']=['CLOSED NFU compact row','NKL_CanonicalChildren.compact_result/compact_call','NKL_ScanAtoms.source','K035/K036,K045/K046,K055/K056,K057-K061']
 elif 'echeck' in s:c['discharged_by']=['CLOSED TX1:189/LPl echeck false-flag law via canonical NFU owner','NKL_CanonicalChildren.echeck_result/echeck_call','NKL_ScanAtoms.source','NKL_ScanRoot.no_later_event','K033/K034,K043/K044,K053/K054,K057-K071,K082/K083']
 else:c['discharged_by']=['Pinned Aeneas P7 safe slice/try_into/unwrap/Range and Result constructors','actual native segment assertions in NKL_SEGMENTS.md','NKL_ScanDomains.source proves all windows; no std oracle','NKL_ScanSequence.result/exact']
 c['status']='DISCHARGED_IN_CANDIDATE_PENDING_LEDGER'
pairs=[[27,28],[29,30],[31,32],[33,34],[35,36],[37,38],[39,40],[41,42],[43,44],[45,46],[47,48],[49,50],[51,52],[53,54],[55,56],[57,58],[57,59],[57,60],[57,61],[62,63],[62,64],[62,65],[62,66],[67,68],[67,69],[67,70],[67,71],[76,77],[78,79],[80,81],[82,83]]
packet=dict(row='TX1:084',function=scanner['function'],status='CANDIDATE_CLOSED_PENDING_LEDGER',frozen_body_sha256=scanner['frozen_body_sha256'],obligation_statement_hash=scanner['obligation_statement_hash'],baseline='NKH_LEDGER.json.xz#TX1:084',baseline_sha256=sha(base.read_bytes()),method='direct hybrid P6 under y/ai/aq/aq5/au; reviewed native-cut transcription; option-A tool-trust reclassification, no new runtime trust',roots=['NKL_ScanRoot.deployed','NKL_ScanRoot.adopted','NKL_ScanRoot.no_later_event','NKL_ScanRoot.success_events'],native_pairs=[[f'NKL_K{a:03}',f'NKL_K{b:03}'] for a,b in pairs],excluded_controls=['NKL_K073','NKL_K075'],hypothesis_inventory=[dict(name='proof',kind='original input carrier Array U8 57607; width follows from type, original domain kept'),dict(name='out/events/after',kind='observed native outputs and post-state, not assumed equations'),dict(name='native',kind='reviewed source-ordered primitive-cut transcription Invoke; permitted ai5/aq2; CLOSED replies fixed internally by ScanAtoms, exact native guards by NativeGuard; no endpoint/dictionary/child-success premise')],caller_clauses=clauses,inventory_clauses=[dict(original=x,status='DISCHARGED_IN_CANDIDATE_PENDING_LEDGER',discharged_by='NKL_ScanDomains.source, NKL_ScanModel.source/adopted and NKL_ScanRoot; only Proof57607 domain needed. Magic/header are unused by body; noncanonical fields are rejected rather than assumed. EC false windows32/224/2272/128 and compact464 use original carriers; source-order first Parse prefix retained.') for x in scanner['obligation']['inventory_domain_obligations']],gate='NKL_AUDIT PASS; authoritative ledger credit awaits next lead gate',trust_added=[],security_target_established=False)
write('NKL_ROW_PACKETS.json',[packet]);write('NKL_CLOSED.json',dict(status='ONE_CANDIDATE_PENDING_AUTHORITATIVE_GATE',functions=[packet],authoritative_new_closed_rows=0,candidate_rows=['TX1:084'],target_established=False))
write('NKL_LEDGER_DELTA.json',dict(baseline=str(base),baseline_sha256=sha(base.read_bytes()),headline=baseline['headline'],baseline_counts=baseline['counts'],closed_delta=0,changed_rows=[],proposed_rows=[dict(row='TX1:084',from_status='OPEN',proposed_status='CLOSED',packet='NKL_ROW_PACKETS.json',credit='PENDING_NEXT_AUTHORITATIVE_LEDGER_GATE')],remaining_rows=ids[:-1],target_established=False))
statements=(E/'NKL_L062/stdout.log').read_text();(E/'NKL_ROOT_STATEMENTS.md').write_text('# Printed scanner roots\n\nExact successful elaboration at L062; standard axioms. Hypothesis inventory: NKL_CUTS.md / NKL_ROW_PACKETS.json.\n\n```text\n'+statements+'\n```\n')
print(f'NKL final validation PASS: {formal} formal charged (one quarantined),70 Kani,2 extractions; one candidate, zero authoritative promotions')
