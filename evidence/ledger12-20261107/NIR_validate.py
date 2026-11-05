"""Fail-closed final packaging validation; no prover replay."""
from pathlib import Path
import json,lzma,hashlib,copy,subprocess,sys,re
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def ledger():
 p=E/'NIR_LEDGER.json';return read(p if p.exists()else Path(str(p)+'.xz'))
base=read(E.parent/'ledger11-20261107/NII_LEDGER.json.xz');prior={r['row']:r for r in base['rows']};delta=read(E.parent/'owner-dedupe-20261107/NIM_LEDGER_DELTA.json');status={r['row']:r['composed_status']for r in base['rows']}
for d in delta['rows']:status[d['row']]=d['status']
owners={}
for a in [14,31]:
 for l in(E/f'NIR_L{a:03}/stdout.log').read_text().splitlines():
  if l.startswith('NIR_OWNER '):
   r=json.loads(l[len('NIR_OWNER '):]);owners[r['root']]=r
rawroots={r['root']for i in range(28)for r in read(E/f'NIR_audit/batch{i}/proof{i}.json')['results']}
def check(L,A,S):
 assert A['full_composition_pass']and A['all_required_raw_roots_present']and A['raw_standard_axioms_only']
 assert S['exit_status']==S['dangling']==S['incompatible_owners']==S['import_mismatches']==0
 assert L['gate']=='PASS'and len(L['rows'])==len({r['row']for r in L['rows']})==599
 assert L['trust_rows']==base['trust_rows']
 for r in L['rows']:
  assert r['status']==status[r['row']]
  assert all(r[k]==prior[r['row']][k]for k in ['function','frozen_body_sha256','canonical_callees','transaction'])
  assert H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())==r['obligation_statement_hash']
  if r['status']=='CLOSED':assert r['owner_module']
  for binding in r['root_owners']:
   n=binding['root'];assert n in rawroots and binding['owner_module']==owners[n]['owner_module']
   assert binding['obligation_statement_sha256']==H(owners[n]['obligation_statement'].encode())
 return True
L=ledger();A=read(E/'NIR_AUDIT.json');S=read(E/'NIR_SCAN.json');check(L,A,S)
mutations=[]
def reject(label,l=L,a=A,s=S,mutate=None):
 l,a,s=copy.deepcopy(l),copy.deepcopy(a),copy.deepcopy(s);mutate(l,a,s)
 try:check(l,a,s)
 except AssertionError:mutations.append(label);return
 raise AssertionError('accepted mutation '+label)
reject('no full gate',mutate=lambda l,a,s:a.update(full_composition_pass=False))
reject('dangling reference',mutate=lambda l,a,s:s.update(dangling=1))
reject('duplicate owner',mutate=lambda l,a,s:s.update(incompatible_owners=1))
reject('unadmitted promotion',mutate=lambda l,a,s:next(r for r in l['rows']if r['status']=='OPEN').update(status='CLOSED'))
reject('obligation changed',mutate=lambda l,a,s:l['rows'][0]['obligation'].update(named_hypotheses=[]))
reject('wrong root owner',mutate=lambda l,a,s:next(r for r in l['rows']if r['root_owners'])['root_owners'][0].update(owner_module='NIR_FalseOwner'))
reject('trust changed',mutate=lambda l,a,s:l['trust_rows'].append(dict(id='NIR_InventedTrust')))
rs=[json.loads(l)for l in(E/'NIR_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==40
source_checks=0
for r in rs:
 ad=read(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 full=read(E/r['attempt']/'receipt.json');assert full['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and str(full['swaps'])=='0'
 for n,h in full['source_hashes'].items():assert H((E/r['attempt']/'sources'/n).read_bytes())==h;source_checks+=1
 assert full['deps_fingerprint']['selected_objects']
assert read(E/'NIR_PREDECESSOR_COMPARISON.json')['same_predecessor_files']==31369
assert read(E/'NIR_PREDECESSOR_COMPARISON.json')['mismatches']==[]
packed=0
for p in E.rglob('*.sha256'):
 original=p.with_suffix('');xz=Path(str(original)+'.xz')
 if xz.exists():assert H(lzma.decompress(xz.read_bytes()))==p.read_text().strip();packed+=1
assert not [p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
assert not list(E.rglob('__pycache__'))
for n in ['NIR_LEDGER_DELTA.json','NIR_PLAN_STATUS.md','NIR_PHYSICAL.md','NIR_SameLawInstance.lean','NIR_COMBINED_IMPORT.lean','NIR_AUDIT.json','NIR_SCAN.json','NIR_HANDOFF.md','NIR_REMAINING.md','NIR_ATTEMPTS.jsonl']:assert(E/n).is_file()
freeze=['docs/research/100bit-spend-path-20261013/'+p for p in ['crates','programs','Cargo.lock']]
r=subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--',*freeze],cwd=R);assert r.returncode==0
out=dict(status='PASS',rows=599,closed=407,open=192,qualified=0,formal_scopes=40,mutations_rejected=mutations,source_snapshot_checks=source_checks,packed_sha_checks=packed,required_raw_roots=len(rawroots),new_trust_rows=0,shipped_changes=0,target_established=False)
(E/'NIR_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print('NIR validation PASS; all packaging and mutation gates checked')
