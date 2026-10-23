"""Verify focused receipts and field dispositions without rerunning proofs."""
from pathlib import Path
import json,hashlib,re,subprocess,sys
R=Path(__file__).resolve().parents[2];D=R/'docs/research/100bit-spend-path-20261013';E=D/'evidence/s2x-20261023'
selected={'S2X_ChildRetention':5,'S2X_SnapshotWrite':3,'S2X_RuntimeRetention':8,'S2X_SecondCut':12,'S2X_Fields':13,'S2X_Audit':14}
allowed={'propext','Classical.choice','Quot.sound'}; accepted=[];names=set()
for module,n in selected.items():
 p=D/'lean'/(module+'.lean');s=p.read_text();receipt=E/f'lean-{n:03d}'/'receipt.json';x=json.loads(receipt.read_text());name=p.name
 assert x['exit_status']==0 and x['source_hashes'][name]==hashlib.sha256(p.read_bytes()).hexdigest(),module
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert x['swaps']=='0'; assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option\s+(maxHeartbeats|maxRecDepth)',s,re.M)
 reports=x['print_axioms'];assert reports
 theorem_names=re.findall(r'^theorem (\w+)',s,re.M)
 for report in reports:
  nm=report.split("'")[1];names.add(nm)
  if 'depends on axioms:' in report:
   axioms={a.strip() for a in report.split('[',1)[1].split(']',1)[0].split(',')};assert axioms<=allowed,report
 for nm in theorem_names:assert any("'AspisR1.S2X."+nm+"'" in line for line in reports),nm
 accepted.append(dict(module=module,attempt=n,receipt=str(receipt.relative_to(R)),receipt_sha256=hashlib.sha256(receipt.read_bytes()).hexdigest(),exit_status=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps'],source_revision=x['source_revision'],source_sha256=x['source_hashes'][name],deps_fingerprint=x['deps_fingerprint'],print_axioms=reports))
allreceipts=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/receipt.json'))]
preflights=[json.loads(p.read_text()) for p in sorted(E.glob('lean-*/preflight.json'))]
assert len(allreceipts)+len(preflights)<=100
base=json.loads((E/'lean-001/receipt.json').read_text())['source_revision']
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
assert all(p.startswith(('tools/s2x-20261023/','docs/research/100bit-spend-path-20261013/evidence/s2x-20261023/','docs/research/100bit-spend-path-20261013/lean/S2X_')) for p in changed),changed
cache=json.loads((E/'reused-cache.json').read_text())
r9=next(r for r in cache['copied'] if r['module']=='R9PoolRuntimeBinding')
assert r9['objects'][0]['sha256']=='91058b7a2d4e7196685815142fe5adbcbb85c1004282a5e383188879bd99ad83'
fields={
 'proofSuffix':dict(status='conditional',proved='actual TX1 and TX2 selected suffix shapes',retained=['range1','range2','length1','length2','writtenCut','currentCut','observed1','observed2','p2prime','matched']),
 'checkpointBytes':dict(status='conditional',proved='checkpoint_persistence and checkpoint_sites',retained=['CheckpointVersionBinding','saveCut','tx2Cut','resumeCut']),
 'checkpointLength':dict(status='conditional',proved='accepted_checkpoint_length on actual whole owned TX1',retained=['OwnedSnapshotShape','entrySize','savedAtWrite']),
 'accountFrame':dict(status='open',proved='SDK primitive and CP-only logical commit frames',retained=['native snapshot/write wrapper refinement','OpaqueChildFrame','full actual account observations']),
 'writtenMetadata':dict(status='open',proved='commit_metadata for full Account records',retained=['native metadata interpretation and snapshot/copy/child-effect composition']),
 'ChildInputRetention':dict(status='open: universal port obstructed',proved='fixed owned values retained; constant pure op11 counterexample',retained=['invocation-indexed port correction','actual child-site observations and opaque native frames'])}
out=dict(schema='focused-extractor-proof-packet-v1',target='S2-X owned snapshot/checkpoint/cross-transaction fields',base_revision=base,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),selected=accepted,distinct_standard_only_axiom_reports=len(names),lean_compile_attempts=len(allreceipts),preflight_failures=len(preflights),budget_charged_conservatively=len(allreceipts)+len(preflights),lean_budget=100,kani_runs=0,kani_budget=60,all_lean_attempts=[dict(attempt=x['attempt'],exit_status=x['exit_status'],wall_seconds=x['wall_seconds'],peak_rss_kib=x['peak_rss_kib'],swaps=x['swaps']) for x in allreceipts],fields=fields,shipped_source_changed=False,elf_rebuilt=False,coherent_release_replay=False,s2_closed=False,changed_paths=changed)
if '--check' not in sys.argv:
 (E/'manifest.json').write_text(json.dumps(out,indent=2)+'\n')
else:
 old=json.loads((E/'manifest.json').read_text())
 for k in ['selected','fields','lean_compile_attempts','preflight_failures','budget_charged_conservatively','kani_runs','distinct_standard_only_axiom_reports']:
  assert old[k]==out[k],k
print(json.dumps({k:out[k] for k in ['distinct_standard_only_axiom_reports','lean_compile_attempts','preflight_failures','budget_charged_conservatively','kani_runs','s2_closed']}))
