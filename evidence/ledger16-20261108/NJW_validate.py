"""Receipt/obligation validation only; no prover or native compilation."""
from pathlib import Path
import json,lzma,hashlib,copy,subprocess,collections,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];P=E.parent/'ledger15-20261108';H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):return lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes()
def J(p):return json.loads(raw(p))
def need(ok,why):
 if not ok:raise ValueError(why)
def verify(L,D,A,S,C):
 B=J(P/'NJO_LEDGER.json.xz');old={r['row']:r for r in B['rows']};new={r['row']:r for r in L['rows']};review={r['row']:r for r in C['rows']};parents=J(E/'NJW_PARENT_CLAUSES.json');parentids=set(parents['parents']);expected={'TX2:150','TX2:157','TX2:206','TX2:208','TX1:133','TX1:134','TX1:142','TX1:305','TX1:306'}|{f'TX1:{i:03}'for i in[208,209,214,216,217,219,227,228,229,231,244,247]}
 need(len(L['rows'])==len(new)==599,'inventory')
 need(len(D['new_closed_rows'])==21 and set(D['new_closed_rows'])==expected and set(review)==expected,'candidate set/double count')
 need({k for k in new if new[k]['status']!=old[k]['status']}==expected,'extra promotion')
 need(L['trust_rows']==B['trust_rows']and not D['trust_rows_changed'],'trust change')
 need(L['counts']==dict(collections.Counter(r['status']for r in L['rows']))=={'CLOSED':484,'OPEN':115},'counts')
 need(not L['security_target_established']and not A['cold_release_replay'],'target overclaim')
 need(A['full_composition_pass']and A['all_required_raw_roots_present']and A['raw_standard_axioms_only'],'raw gate')
 need(A['required_roots']==len(J(E/'NJW_AUDIT_ROOTS.json')['roots']),'missing root')
 need(S['exit_status']==0 and S['dangling']==S['incompatible_owners']==S['import_mismatches']==S['canonical_duplicate_owners']==0,'scan')
 need(len(A['fixtures'])==8 and A['same_optimized_proof_binary_sha256'],'fixtures')
 for rid,r in new.items():
  p=old[rid]
  if rid not in expected|parentids:need(r==p,'uncredited change '+rid);continue
  need(all(r[k]==p[k]for k in['function','frozen_body_sha256','canonical_callees','transaction']),'source identity '+rid)
  need(r['obligation_statement_hash']==H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode()),'obligation hash '+rid)
  o=r['obligation'];po=p['obligation']
  if rid in expected:
   need(p['status']=='OPEN'and r['status']=='CLOSED','status/double count')
   need(o['basis_obligation']==po,'basis clauses')
   need(r['root_owners']==[dict(root=x['root'],owner_module=x['owner_module'],obligation_statement_sha256=H(x['obligation_statement'].encode()))for x in review[rid]['kernel_statements']],'canonical roots')
   need(r['owner_module']==next(k['owner_module']for k in review[rid]['kernel_statements']if k['root']==review[rid]['primary_root']),'primary owner')
   need(not review[rid]['hypothesis_inventory'].get('extra_logical_hypotheses')and not review[rid]['hypothesis_inventory'].get('endpoint_or_success_premises'),'banned root premise')
  if rid in parentids:need(o['NJW_parent_basis_obligation']==po,'parent original')
  for k in['named_hypotheses','inventory_domain_obligations']:need(o[k]==po[k],'lost original '+rid)
  cs=o['caller_domain_obligations'];n=len(po['caller_domain_obligations']);need(cs[:n]==po['caller_domain_obligations'],'caller loss')
  additions=[c['caller_clause']for c in parents['clauses']if c['parent']==rid]
  need(cs[n:]==additions,'own domain silently dropped')
  if rid not in expected:need(r['status']==p['status'],'parent promotion')
 need(new['TX2:115']==old['TX2:115'],'115 changed instead of supplemented')
 supp=L['supplemental_child_obligations'];need(len(supp)==1 and supp[0]['id']=='NJW-aw-TX2:115-off-domain'and supp[0]['status']=='OPEN'and not supp[0]['new_game_premise'],'missing aw child')
 need(J(E/'NJW_PREDECESSOR_COMPARISON.json')['status']=='PASS','cache drift')
 need(J(E/'NJW_NJI_EMISSION.json')['status']=='PASS_FOUR_CANDIDATE_BODIES_EMITTED','emitted bodies')
 need(J(E/'NJW_NJM_INHERITED_NATIVE.json')['status']=='PASS','rounds cut native pairing')
 return True

def main():
 need(H(lzma.decompress((P/'NJO_LEDGER.json.xz').read_bytes()))==(P/'NJO_LEDGER.json.sha256').read_text().split()[0],'basis uncompressed hash')
 L=J(E/'NJW_LEDGER.json.xz');D=J(E/'NJW_LEDGER_DELTA.json');A=J(E/'NJW_AUDIT.json');S=J(E/'NJW_SCAN.json');C=J(E/'NJW_CANDIDATE_REVIEW.json');verify(L,D,A,S,C)
 attempts=[json.loads(l)for l in(E/'NJW_ATTEMPTS.jsonl').read_text().splitlines()];need(len(attempts)==len({r['attempt']for r in attempts})==40,'budget');sourcechecks=0
 for a in attempts:
  rc=J(E/a['attempt']/'receipt.json');ad=J(E/(a['attempt']+'-admission.json'));need(ad['exit']==0 and ad['reservation']['allowed']is True,'admission')
  need(rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'caps')
  need(str(rc['swaps'])=='0','swap');need(rc['source_revision']and rc['command']and rc['wall_seconds']>=0 and rc['deps_fingerprint']['selected_objects'],'section6')
  if rc['kind']=='lean':need('-M7000'in rc['command'],'Lean cap')
  for n,h in rc['source_hashes'].items():
   p=E/a['attempt']/'sources'/n
   if not p.exists():p=Path(str(p)+'.xz')
   need(p.exists()and H(raw(p))==h,'source snapshot '+str(p));sourcechecks+=1
  need(rc['exit_status']==0 or a['attempt']in A['retained_nonzero_audit_exits'],'unexplained nonzero')
 results=[]
 for i in range(30):results+=J(E/f'NJW_audit/batch{i}/proof{i}.json')['results']
 need(len(results)==len({r['root']for r in results})==A['required_roots'],'all-root coverage')
 need(all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in results),'axioms')
 need([r['root']for r in results if not r['equal']]==['NHC_DecodeModel.decoder_error'],'retained finding')
 for p in E.glob('NJW_L[0-9][0-9][0-9]/NJW_ProofDriver_BINARY_PIN.json'):need(J(p)['sha256']==A['same_optimized_proof_binary_sha256'],'different proof binary')
 for r in J(E/'NJW_INPUT_PINS.json'):need(H((R/r['path']).read_bytes())==r['sha256'],'input drift '+r['path'])
 packed=0
 for p in E.rglob('*.sha256'):
  q=Path(str(p)[:-7]+'.xz')
  if q.exists():need(H(lzma.decompress(q.read_bytes()))==p.read_text().split()[0],'compressed sha '+str(q));packed+=1
 need(not any(p.is_file()and p.stat().st_size>20_000_000 for p in E.rglob('*')),'oversize')
 # Mutation tests protect the concrete gate, original clauses and scope, not a mirror of theorem proofs.
 mutations=[]
 for name,mut in[
  ('extra_row',lambda l,d,a,s,c:next(r for r in l['rows']if r['row']=='TX1:129').update(status='CLOSED')),
  ('lost_caller',lambda l,d,a,s,c:next(r for r in l['rows']if r['row']=='TX2:150')['obligation']['caller_domain_obligations'].clear()),
  ('lost_domain',lambda l,d,a,s,c:next(r for r in l['rows']if r['row']=='TX1:136')['obligation']['caller_domain_obligations'].pop()),
  ('trust',lambda l,d,a,s,c:l['trust_rows'].append('invented')),
  ('missing_root',lambda l,d,a,s,c:a.update(all_required_raw_roots_present=False)),
  ('dangling',lambda l,d,a,s,c:s.update(dangling=1)),
  ('duplicate',lambda l,d,a,s,c:s.update(canonical_duplicate_owners=1)),
  ('target',lambda l,d,a,s,c:l.update(security_target_established=True)),
  ('aw_supplement',lambda l,d,a,s,c:l.update(supplemental_child_obligations=[])),
  ('extra_premise',lambda l,d,a,s,c:c['rows'][0]['hypothesis_inventory']['extra_logical_hypotheses'].append('child success'))]:
  args=copy.deepcopy([L,D,A,S,C]);mut(*args)
  try:verify(*args)
  except(ValueError,KeyError,AssertionError):mutations.append(dict(control=name,rejected=True))
  else:raise AssertionError('mutation accepted '+name)
 x=dict(status='PASS',sources_checked=sourcechecks,compressed_sha_pairs=packed,input_pins=len(J(E/'NJW_INPUT_PINS.json')),mutations=mutations,scopes=40,raw_roots=len(results),new_closed=21,no_trust_row_change=True,no_shipped_change=True,security_target_established=False)
 (E/'NJW_VALIDATION.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(status='PASS',mutations=len(mutations),sources_checked=sourcechecks,compressed_pairs=packed)))
if __name__=='__main__':main()
