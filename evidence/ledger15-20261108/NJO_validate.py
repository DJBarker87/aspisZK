"""Validate ledger, immutable inputs and exact retained receipts; never run a prover."""
from pathlib import Path
import json,lzma,hashlib,copy,subprocess,re,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):return lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes()
def J(p):return json.loads(raw(p))
def require(ok,msg):
 if not ok:raise ValueError(msg)
def verify(L,D,A,S,C):
 B=J(E.parent/'ledger14-20261108/NJK_LEDGER.json.xz');old={r['row']:r for r in B['rows']};new={r['row']:r for r in L['rows']};parents={'TX1:127','TX2:093'}
 expected={f'TX1:{n:03}'for n in list(range(118,127))+[128,302,303,304,307,268]}|{f'TX2:{n:03}'for n in list(range(84,93))+[94]}
 require(len(L['rows'])==len(new)==599,'inventory')
 require(len(D['new_closed_rows'])==25 and set(D['new_closed_rows'])==expected,'candidate set/double count')
 require({k for k in new if new[k]['status']!=old[k]['status']}==expected,'extra promotion')
 require(L['trust_rows']==B['trust_rows']and not D['trust_rows_changed'],'trust change')
 require(not L['security_target_established']and not A['cold_release_replay'],'target overclaim')
 require(A['full_composition_pass']and A['all_required_raw_roots_present']and A['raw_standard_axioms_only'],'raw gate')
 require(A['required_roots']==len(J(E/'NJO_AUDIT_ROOTS.json')['roots']),'missing root')
 require(S['exit_status']==0 and S['dangling']==S['incompatible_owners']==S['import_mismatches']==S['canonical_duplicate_owners']==0,'scan')
 require(len(A['fixtures'])==8 and A['same_optimized_proof_binary_sha256'],'fixtures')
 cr={r['row']:r for r in C['rows']};require(set(cr)==expected,'review inventory')
 for rid,r in new.items():
  p=old[rid]
  if rid not in expected|parents:require(r==p,'uncredited change '+rid);continue
  require(all(r[k]==p[k]for k in ['function','frozen_body_sha256','canonical_callees','transaction']),'source identity '+rid)
  require(r['obligation_statement_hash']==H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode()),'obligation hash '+rid)
  if rid in expected:
   require(p['status']=='OPEN'and r['status']=='CLOSED','status/double count')
   require(r['obligation']['basis_obligation']==p['obligation'],'basis clauses')
   for k in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']:require(r['obligation'][k]==p['obligation'][k],'lost original '+rid)
   require(cr[rid]['roots'][0]==r['root_owners'][0]['root'],'owner root')
   require(r['root_owners'][0]['owner_module']==cr[rid]['kernel_statements'][0]['owner_module'],'canonical owner')
   require(not cr[rid]['hypothesis_inventory'].get('extra_logical_hypotheses')and not cr[rid]['hypothesis_inventory'].get('endpoint_or_success_premises'),'banned root premise')
  else:
   require(r['status']=='OPEN','parent promotion')
   require(r['obligation']['NJO_basis_obligation']==p['obligation'],'parent basis')
   for k in ['named_hypotheses','inventory_domain_obligations']:require(r['obligation'][k]==p['obligation'][k],'parent original')
   cs=r['obligation']['caller_domain_obligations'];n=len(p['obligation']['caller_domain_obligations']);require(cs[:n]==p['obligation']['caller_domain_obligations'],'parent caller loss')
   required=[c['caller_clause']for c in J(E/'NJO_PARENT_CLAUSES.json')['clauses']if c['parent']==rid]
   require(cs[n:]==required and len(required)==10 and all(c['status']=='OPEN'and c['discharged_by']is None for c in required),'unit domain silently dropped')
 require(new['TX1:142']['status']=='OPEN','Ops root promoted')
 require(J(E/'NJO_PREDECESSOR_COMPARISON.json')['status']=='PASS','cache drift')
 return True

def main():
 L=J(E/'NJO_LEDGER.json.xz');D=J(E/'NJO_LEDGER_DELTA.json');A=J(E/'NJO_AUDIT.json');S=J(E/'NJO_SCAN.json');C=J(E/'NJO_CANDIDATE_REVIEW.json');verify(L,D,A,S,C)
 attempts=[json.loads(l)for l in(E/'NJO_ATTEMPTS.jsonl').read_text().splitlines()];require(len(attempts)==len({r['attempt']for r in attempts})==40,'budget')
 sourcechecks=0
 for a in attempts:
  rc=J(E/a['attempt']/'receipt.json');ad=J(E/(a['attempt']+'-admission.json'));require(ad['exit']==0 and ad['reservation']['allowed']is True,'admission')
  require(rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'caps')
  require(str(rc['swaps'])=='0','swap');require(rc['source_revision']and rc['command']and rc['wall_seconds']>=0 and rc['deps_fingerprint']['selected_objects'],'section6')
  if rc['kind']=='lean':require('-M7000'in rc['command'],'Lean cap')
  for n,h in rc['source_hashes'].items():
   p=E/a['attempt']/'sources'/n
   if not p.exists():p=Path(str(p)+'.xz')
   require(p.exists()and H(raw(p))==h,'source snapshot '+str(p));sourcechecks+=1
  require(rc['exit_status']==0 or a['attempt']in A['retained_nonzero_audit_exits'],'unexplained nonzero')
 results=[]
 for i in range(30):results+=J(E/f'NJO_audit/batch{i}/proof{i}.json')['results']
 require(len(results)==len({r['root']for r in results})==A['required_roots'],'all-root coverage')
 require(all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in results),'axioms')
 require([r['root']for r in results if not r['equal']]==['NHC_DecodeModel.decoder_error'],'retained finding')
 for p in E.glob('NJO_L[0-9][0-9][0-9]/NJO_ProofDriver_BINARY_PIN.json'):require(J(p)['sha256']==A['same_optimized_proof_binary_sha256'],'different proof binary')
 for pre in ['NJE','NJB']:require(J(E/f'NJO_{pre}_REVALIDATION.json')['status']=='PASS','native revalidation')
 packed=0
 for p in E.rglob('*.sha256'):
  q=Path(str(p)[:-7]+'.xz')
  if q.exists():require(H(lzma.decompress(q.read_bytes()))==p.read_text().split()[0],'compressed sha '+str(q));packed+=1
 for p in E.glob('NJO_*.lean'):
  require(not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),'forbidden proof')
  require(any(H(p.read_bytes())in J(E/a['attempt']/'receipt.json')['source_hashes'].values()for a in attempts if a['kind']=='lean'and a['exit_status']==0),'uncompiled source')
 pins=J(E/'NJO_INPUT_PINS.json')+J(E/'NJO_READ_PINS.json')
 for pin in pins:require(H((R/pin['path']).read_bytes())==pin['sha256'],'input pin '+pin['path'])
 require(not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000],'oversize')
 require(not list(E.rglob('__pycache__')),'bytecode')
 for pref in ['', 'docs/research/100bit-spend-path-20261013/']:
  require(subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--',*[pref+n for n in ['crates','programs','Cargo.lock']]],cwd=R).returncode==0,'shipped change')
 denied=[]
 def reject(name,mut):
  xs=list(map(copy.deepcopy,[L,D,A,S,C]));mut(*xs)
  try:verify(*xs)
  except ValueError:denied.append(name);return
  raise ValueError('mutation accepted '+name)
 reject('headline overclaim',lambda L,D,A,S,C:L.update(security_target_established=True))
 reject('raw gate missing',lambda L,D,A,S,C:A.update(full_composition_pass=False))
 reject('root missing',lambda L,D,A,S,C:A.update(required_roots=A['required_roots']-1))
 reject('dangling',lambda L,D,A,S,C:S.update(dangling=1))
 reject('owner conflict',lambda L,D,A,S,C:S.update(incompatible_owners=1))
 reject('import mismatch',lambda L,D,A,S,C:S.update(import_mismatches=1))
 reject('fixture loss',lambda L,D,A,S,C:A.update(fixtures=[]))
 reject('double count',lambda L,D,A,S,C:D['new_closed_rows'].append('TX1:268'))
 reject('trust change',lambda L,D,A,S,C:L.update(trust_rows=[]))
 reject('parent promotion',lambda L,D,A,S,C:next(r for r in L['rows']if r['row']=='TX1:127').update(status='CLOSED'))
 reject('unit domain loss',lambda L,D,A,S,C:next(r for r in L['rows']if r['row']=='TX2:093')['obligation']['caller_domain_obligations'].pop())
 reject('extra endpoint hypothesis',lambda L,D,A,S,C:C['rows'][0]['hypothesis_inventory'].update(endpoint_or_success_premises=['success']))
 out=dict(status='PASS',rows=599,admitted=25,scopes=40,source_snapshot_checks=sourcechecks,compressed_sha_checks=packed,input_pins=len(pins),rejected_mutations=denied,trust_rows_changed=False,shipped_changes=0,kani=0,extraction=0)
 (E/'NJO_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
