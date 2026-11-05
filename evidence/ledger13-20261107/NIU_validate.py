"""Fail-closed ledger, complete-obligation, resource and packaging validation."""
from pathlib import Path
import json,lzma,hashlib,copy,subprocess,sys,collections,ast
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def raw(p):return p.read_bytes()if p.exists()else lzma.decompress(Path(str(p)+'.xz').read_bytes())
base=J(E.parent/'ledger12-20261107/NIR_LEDGER.json.xz');prior={r['row']:r for r in base['rows']}
review=J(E/'NIU_CANDIDATE_REVIEW.json');candidates={r['row']:r for r in review['rows']};assert len(candidates)==25
owners={}
for l in raw(E/'NIU_L003/stdout.log').decode().splitlines():
 if l.startswith('NIU_OWNER '):
  x=json.loads(l[len('NIU_OWNER '):]);owners[x['root']]=x
roots=[x for i in range(30)for x in J(E/f'NIU_audit/batch{i}/proof{i}.json')['results']];rawroots={r['root']for r in roots}
assert len(roots)==len(rawroots)==8182 and rawroots==set(J(E/'NIU_AUDIT_ROOTS.json')['roots'])
assert all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in roots)
loaded={r['module']for r in map(json.loads,(E/'NIU_LOADED_scan.jsonl').read_text().splitlines())}
def check(L,A,S,D):
 assert A['full_composition_pass']and A['all_required_raw_roots_present']and A['raw_standard_axioms_only']
 assert S['exit_status']==S['dangling']==S['incompatible_owners']==S['import_mismatches']==0
 assert L['gate']=='PASS'and len(L['rows'])==len({r['row']for r in L['rows']})==599
 assert L['trust_rows']==base['trust_rows'] and not D['trust_rows_changed']
 assert D['new_count']==25 and set(D['new_closed_rows'])==set(candidates)
 assert collections.Counter(r['status']for r in L['rows'])=={'CLOSED':432,'OPEN':167}
 for r in L['rows']:
  old=prior[r['row']]
  assert all(r[k]==old[k]for k in ['function','frozen_body_sha256','canonical_callees','transaction'])
  assert H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode())==r['obligation_statement_hash']
  if r['row']not in candidates:assert r==old
  else:
   c=candidates[r['row']];assert old['status']=='OPEN'and r['status']=='CLOSED'
   assert r['obligation']['basis_obligation']==old['obligation']
   assert r['obligation']['certificate']==c['certificate']and c['root_domain']==c['certificate']['root_domain']and c['root_domain']
   assert r['obligation']['NIU_semantic_review']==c['semantic_review']
   assert r['obligation']['kernel_roots']==c['complete_kernel_statements']
   assert r['obligation']['NIU_complete_clause_review']==c['basis_clauses']
   for k in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']:assert r['obligation'][k]==old['obligation'][k]
  if r['status']=='CLOSED':assert r['owner_module']
  for x in r['root_owners']:
   n=x['root'];assert n in rawroots and x['owner_module']==owners[n]['owner_module']and x['owner_module']in loaded
   assert x['obligation_statement_sha256']==H(owners[n]['obligation_statement'].encode())
 for rid in ['TX1:137','TX1:136','TX2:065','TX2:129','TX2:115']:assert next(r for r in L['rows']if r['row']==rid)['status']=='OPEN'
 assert next(r for r in L['rows']if r['row']=='TX1:147')==prior['TX1:147']
 return True
L=J(E/'NIU_LEDGER.json.xz');A=J(E/'NIU_AUDIT.json');S=J(E/'NIU_SCAN.json');D=J(E/'NIU_LEDGER_DELTA.json');check(L,A,S,D)
mutations=[]
def reject(label,fn):
 l,a,s,d=map(copy.deepcopy,[L,A,S,D]);fn(l,a,s,d)
 try:check(l,a,s,d)
 except AssertionError:mutations.append(label);return
 raise AssertionError('accepted mutation '+label)
reject('no full gate',lambda l,a,s,d:a.update(full_composition_pass=False))
reject('dangling reference',lambda l,a,s,d:s.update(dangling=1))
reject('duplicate owner',lambda l,a,s,d:s.update(incompatible_owners=1))
reject('unadmitted parent promotion',lambda l,a,s,d:next(r for r in l['rows']if r['row']=='TX1:137').update(status='CLOSED'))
reject('candidate not promoted',lambda l,a,s,d:next(r for r in l['rows']if r['row']in candidates).update(status='OPEN'))
reject('obligation changed',lambda l,a,s,d:next(r for r in l['rows']if r['row']in candidates)['obligation'].update(named_hypotheses=[dict(name='NIU_InventedPremise')]))
reject('caller success premise inserted',lambda l,a,s,d:next(r for r in l['rows']if r['row']in candidates)['obligation'].update(success=True))
reject('wrong root owner',lambda l,a,s,d:next(r for r in l['rows']if r['root_owners'])['root_owners'][0].update(owner_module='NIU_FalseOwner'))
reject('trust changed',lambda l,a,s,d:l['trust_rows'].append(dict(id='NIU_InventedTrust')))
reject('double-count corrected import147',lambda l,a,s,d:d['new_closed_rows'].append('TX1:147'))
reject('drop candidate clause',lambda l,a,s,d:next(r for r in l['rows']if r['row']in candidates)['obligation'].update(caller_domain_obligations=[]))
rs=[json.loads(l)for l in(E/'NIU_ATTEMPTS.jsonl').read_text().splitlines()];assert len(rs)==40
source_checks=0
for r in rs:
 ad=J(E/(r['attempt']+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
 rc=J(E/r['attempt']/'receipt.json');assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and str(rc['swaps'])=='0'
 assert rc['env']['CARGO_TARGET_DIR']=='/home/dombarker/project-offloads/codex-cx-ledger13-20261107/NIU_target'
 for n,h in rc['source_hashes'].items():assert H(raw(E/r['attempt']/'sources'/n))==h;source_checks+=1
 assert rc['deps_fingerprint']['selected_objects']
assert J(E/'NIU_PREDECESSOR_COMPARISON.json')['mismatches']==[]
packed=0
for p in E.rglob('*.sha256'):
 q=p.with_suffix('');xz=Path(str(q)+'.xz')
 if xz.exists():assert H(lzma.decompress(xz.read_bytes()))==p.read_text().strip();packed+=1
assert not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
assert not list(E.rglob('__pycache__'))
assert not[p for p in E.rglob('*')if p.is_file()and p.suffix in['.olean','.ir','.o','.a','.so','.elf']]
for n in ['NIU_LEDGER_DELTA.json','NIU_PLAN_STATUS.md','NIU_PHYSICAL.md','NIU_COMBINED_IMPORT.lean','NIU_AUDIT.json','NIU_SCAN.json','NIU_HANDOFF.md','NIU_REMAINING.md','NIU_ATTEMPTS.jsonl']:assert(E/n).is_file()
for p in E.glob('NIU_*.py'):ast.parse(p.read_text())
freeze=['docs/research/100bit-spend-path-20261013/'+p for p in['crates','programs','Cargo.lock']];assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--',*freeze],cwd=R).returncode==0
pool=J(E/'NIU_PHYSICAL.json');assert pool['b']['b']=={'CLOSED':36,'OPEN':17}and pool['b']['c']=={'CLOSED':396,'OPEN':150};assert len(pool['Pool']['exclusive_owners'])==13 and pool['Pool']['held_sites_closed']==0
out=dict(status='PASS',rows=599,closed=432,open=167,qualified=0,formal_scopes=40,mutations_rejected=mutations,source_snapshot_checks=source_checks,packed_sha_checks=packed,required_raw_roots=len(rawroots),new_trust_rows=0,shipped_changes=0,target_established=False)
(E/'NIU_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
