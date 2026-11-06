"""Validate retained evidence and reject overclaims; never execute a prover."""
from pathlib import Path
import json,lzma,hashlib,subprocess,copy,re,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):return lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes()
def J(p):return json.loads(raw(p))
def require(ok,msg):
 if not ok:raise ValueError(msg)
def verify(ledger,delta,audit,scan,review):
 old=J(E.parent/'ledger13-20261107/NIU_LEDGER.json.xz');before={r['row']:r for r in old['rows']};after={r['row']:r for r in ledger['rows']}
 require(len(ledger['rows'])==len(after)==599,'row inventory/duplicate row')
 required={'TX2:129','TX2:115','TX1:156','TX1:215','TX1:329','TX2:212'}
 require(set(delta['new_closed_rows'])==required and len(delta['new_closed_rows'])==6,'admitted set or double count')
 require({rid for rid,r in after.items()if r['status']!=before[rid]['status']}==required,'extra promotion')
 require(ledger['trust_rows']==old['trust_rows']and delta['trust_rows_changed']is False,'trust changed')
 require(not ledger['security_target_established']and audit['cold_release_replay']is False,'headline/release overclaim')
 require(audit['full_composition_pass']and audit['raw_standard_axioms_only']and audit['all_required_raw_roots_present'],'missing raw gate')
 require(scan['exit_status']==0 and scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0,'scan failure')
 require(len(audit['fixtures'])==8 and audit['same_optimized_proof_binary_sha256'],'fixture gate')
 require(audit['required_roots']==len(J(E/'NJK_AUDIT_ROOTS.json')['roots']),'dropped root')
 cr={r['row']:r for r in review['rows']};require(len(cr)==7,'candidate inventory')
 for rid,r in after.items():
  p=before[rid]
  if rid not in required:require(r==p,'changed uncredited row '+rid);continue
  require(p['status']=='OPEN'and r['status']=='CLOSED','prior status/double count')
  require(r['obligation']['basis_obligation']==p['obligation'],'basis obligation changed')
  for k in ['named_hypotheses','inventory_domain_obligations','caller_domain_obligations']:require(r['obligation'][k]==p['obligation'][k],'dropped original clause '+rid)
  require(all(r[k]==p[k]for k in ['function','frozen_body_sha256','canonical_callees','transaction']),'source/domain identity')
  require(cr[rid]['admissible']and cr[rid]['primary_root']==r['root_owners'][0]['root'],'canonical primary owner')
  require(r['obligation_statement_hash']==H(json.dumps(r['obligation'],sort_keys=True,separators=(',',':')).encode()),'complete obligation hash')
 require('NIG_FinishInput.Domain'in after['TX2:115']['obligation']['NJK_semantic_review']['caller'],'Domain caller clause dropped')
 require('SAME-call' in cr['TX2:129']['semantic_review']['caller'],'nested pair domain widened')
 require(after['TX1:142']['status']=='OPEN'and not cr['TX1:142']['admissible'],'generic Ops root admitted')
 require(J(E/'NJK_OBSERVER_PROVENANCE.json')['status']=='PASS_CANONICAL_PINNED_EMISSION_AND_FROZEN_OBSERVER_BODY','observer provenance missing')
 require(J(E/'NJK_PREDECESSOR_COMPARISON.json')['status']=='PASS','predecessor object changed')
 return True

def main():
 ledger=J(E/'NJK_LEDGER.json.xz');delta=J(E/'NJK_LEDGER_DELTA.json');audit=J(E/'NJK_AUDIT.json');scan=J(E/'NJK_SCAN.json');review=J(E/'NJK_CANDIDATE_REVIEW.json');verify(ledger,delta,audit,scan,review)
 attempts=[json.loads(l)for l in(E/'NJK_ATTEMPTS.jsonl').read_text().splitlines()];require(len(attempts)==40,'scope budget/cadence')
 source_checks=0
 for r in attempts:
  a=r['attempt'];receipt=J(E/a/'receipt.json');ad=J(E/(a+'-admission.json'));require(ad['exit']==0 and ad['reservation']['allowed']is True,'admission')
  require(receipt['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},'resource limits')
  require(str(receipt['swaps'])=='0','swap')
  for n,h in receipt['source_hashes'].items():
   p=E/a/'sources'/n
   if not p.exists():p=Path(str(p)+'.xz')
   require(p.exists()and H(raw(p))==h,'source snapshot '+a+'/'+n);source_checks+=1
  require(receipt['source_revision']and receipt['command']and receipt['wall_seconds']>=0,'section6 fields')
  require(receipt['deps_fingerprint']['selected_objects'],'Aeneas/object pins')
  if receipt['kind']=='lean':require('-M7000'in receipt['command'],'Lean memory option')
 accepted={r['attempt']:r for r in attempts if r['kind']=='lean'and r['exit_status']==0}
 for p in E.glob('NJK_*.lean'):
  require(any(H(p.read_bytes())in r['source_hashes'].values()for r in accepted.values()),'uncompiled current module '+p.name)
  require(not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\s|set_option\s+(maxHeartbeats|maxRecDepth)',p.read_text(),re.M),'forbidden proof '+p.name)
 fixture_pin=J(E/'NJK_L006/NJK_ProofDriver_BINARY_PIN.json')['sha256']
 for p in E.glob('NJK_L[0-9][0-9][0-9]/NJK_ProofDriver_BINARY_PIN.json'):require(J(p)['sha256']==fixture_pin,'different proof binary')
 results=[]
 for i in range(30):results+=J(E/f'NJK_audit/batch{i}/proof{i}.json')['results']
 require(len(results)==len({r['root']for r in results})==audit['required_roots'],'raw root coverage')
 require(all(set(r['walked_axioms'])<={'propext','Classical.choice','Quot.sound'}for r in results),'nonstandard raw axiom')
 require([r['root']for r in results if not r['equal']]==['NHC_DecodeModel.decoder_error'],'unreviewed audit disagreement')
 packed=0
 for p in E.rglob('*.sha256'):
  base=Path(str(p)[:-7]);z=Path(str(base)+'.xz')
  if z.exists():require(H(lzma.decompress(z.read_bytes()))==p.read_text().split()[0],'compressed SHA '+str(z));packed+=1
 inputpins=J(E/'NJK_INPUT_PINS.json')+J(E/'NJK_READ_PINS.json')+J(E/'NJK_OBSERVER_PROVENANCE.json')['pins']
 for r in inputpins:require(H((R/r['path']).read_bytes())==r['sha256'],'input pin '+r['path'])
 require(not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000],'oversized file')
 require(not list(E.rglob('__pycache__')),'bytecode')
 # The freeze is checked at both historical root and established research scope.
 for paths in [['crates','programs','Cargo.lock'],['docs/research/100bit-spend-path-20261013/'+x for x in ['crates','programs','Cargo.lock']]]:
  require(subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','--',*paths],cwd=R).returncode==0,'shipped source changed')
 denials=[]
 def reject(name,mut):
  L,D,A,S,C=map(copy.deepcopy,[ledger,delta,audit,scan,review]);mut(L,D,A,S,C)
  try:verify(L,D,A,S,C)
  except ValueError:denials.append(name);return
  raise ValueError('mutation accepted: '+name)
 reject('false headline',lambda L,D,A,S,C:L.update(security_target_established=True))
 reject('missing raw gate',lambda L,D,A,S,C:A.update(full_composition_pass=False))
 reject('dropped root',lambda L,D,A,S,C:A.update(required_roots=A['required_roots']-1))
 reject('dangling reference',lambda L,D,A,S,C:S.update(dangling=1))
 reject('incompatible owner',lambda L,D,A,S,C:S.update(incompatible_owners=1))
 reject('import mismatch',lambda L,D,A,S,C:S.update(import_mismatches=1))
 reject('missing fixtures',lambda L,D,A,S,C:A.update(fixtures=[]))
 reject('double count residual',lambda L,D,A,S,C:D['new_closed_rows'].append('TX1:215'))
 reject('trust change',lambda L,D,A,S,C:L.update(trust_rows=[]))
 reject('generic dict promotion',lambda L,D,A,S,C:next(r for r in L['rows']if r['row']=='TX1:142').update(status='CLOSED'))
 reject('caller domain removed',lambda L,D,A,S,C:next(r for r in L['rows']if r['row']=='TX2:115')['obligation'].update(caller_domain_obligations=[]))
 reject('canonical owner replaced',lambda L,D,A,S,C:next(r for r in L['rows']if r['row']=='TX1:156')['root_owners'][0].update(root='False.owner'))
 out=dict(status='PASS',rows=599,admitted=6,rejected=1,source_snapshot_checks=source_checks,compressed_sha_checks=packed,input_pins=len(inputpins),rejected_mutations=denials,scopes=40,kani=0,extraction=0,shipped_changes=0,trust_changes=0,security_target_established=False)
 (E/'NJK_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(out))
if __name__=='__main__':main()
