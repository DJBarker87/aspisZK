"""Additive ledger/composition checks; malformed evidence must be rejected."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess,re
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest();STD={'propext','Classical.choice','Quot.sound'}
def raw(p):
 if p.is_file():return p.read_bytes()
 if Path(str(p)+'.xz').is_file():
  b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip();return b
 x=json.loads(Path(str(p)+'.REFERENCE.json').read_text());q=E/x['stored_once'];b=lzma.decompress(q.read_bytes())if x['encoding']=='xz'else q.read_bytes();assert H(b)==x['sha256'];return b
def J(p):return json.loads(raw(p))
def gate(l,a,s,t,c):
 assert l['NHO_coverage']==dict(total=599,CLOSED=335,QUALIFIED=0,OPEN=264)
 assert collections.Counter(r['composed_status']for r in l['rows'])=={'CLOSED':335,'OPEN':264}
 assert len({r['row']for r in l['rows']})==599
 assert not l['NHO_security_target_established']and not l['NHO_cold_release_replay']
 for rid in ['TX1:036','TX1:040','TX1:041','TX1:043','TX1:044']:
  r=next(x for x in l['rows']if x['row']==rid);assert r['composed_status']=='OPEN'and r['NHO_boundary']=='TOOL-BOUNDARY'
 for rid in ['TX1:006','TX1:031']:assert next(r for r in l['rows']if r['row']==rid)['composed_status']=='OPEN'
 expected=J(E/'NHO_AUDIT_ROOTS.json')['roots'];assert a['root_count']==len(expected)==len(a['results'])
 assert {r['root']for r in a['results']}==set(expected)and a['raw_standard_only']
 for row in a['results']:
  assert set(row['walked_axioms'])<=STD
  if not row['equal']:assert row['root']=='NHC_DecodeModel.decoder_error'and set(row['walked_axioms'])==STD and not row['collect_axioms']
 assert {r['root']for r in a['collect_axioms_disagreements']}=={r['root']for r in a['results']if not r['equal']}
 assert len(a['fixtures'])==8
 fx={r['root']:r['walked_axioms']for r in a['fixtures']};assert fx=={'NEP_Planted.matcher':['NEP_Planted.matchAx'],'NEP_Planted.viaPrivate':['NEP_Planted.privateAx'],'NEP_Planted.proof':['NEP_Planted.proofAx'],'NEP_Planted.viaAux':['NEP_Planted.auxAx'],'NEP_MutateMatch.matcher':[],'NEP_MutatePrivate.viaPrivate':[],'NEP_MutateProof.proof':[],'NEP_MutateAux.viaAux':[]}
 assert all(r['equal']for r in a['fixtures'])and a['walker_conformance']['byte_identical']
 assert s['exit_status']==0 and s['status']=='PASS'and s['dangling']==s['incompatible_owners']==s['import_mismatches']==0 and not s['defects']
 assert c['status']=='NONE'and not c['conflicts']and not c['qualified_rows']
 trust={r['id']:r for r in t['rows']};assert trust['RuntimeClockSlotBinding']['status']=='ADDED-LEAD'
 assert trust['ReviewedTranscription-prepared_claim']['status']=='ADDED-LEAD'and trust['ReviewedTranscription-prepared_claim']['direct_closed_rows']==['TX1:193']
 assert trust['RuntimeCpiReadonlyEntry7']['status']=='ADDED-PENDING-LEAD'and not trust['RuntimeCpiReadonlyEntry7']['used']and not trust['RuntimeCpiReadonlyEntry7']['direct_closed_rows']
 assert trust['ReviewedTranscription-polynomial']['status']=='RECLASSIFICATION'and trust['ReviewedTranscription-polynomial']['direct_closed_rows']==['TX2:119']
 assert t['no_trust_removed']
 return True
if __name__=='__main__':
 l=J(E/'NHO_LEDGER.json');a=J(E/'NHO_AUDIT.json');s=J(E/'NHO_SCAN.json');t=J(E/'NHO_TRUST_USED.json');c=J(E/'NHO_CONFLICTS.json');assert gate(l,a,s,t,c)
 old=J(R/'evidence/ledger9-20261105/NGZ_LEDGER.json');changed=[]
 for b,r in zip(old['rows'],l['rows']):
  assert b['row']==r['row']and b['function']==r['function']and b['frozen_body_sha256']==r['frozen_body_sha256']and b['canonical_callees']==r['canonical_callees']
  if b['composed_status']!=r['composed_status']:assert b['composed_status']=='OPEN'and r['composed_status']=='CLOSED';changed.append(r['row'])
 assert len(changed)==32
 proven=[]
 for prefix in ['NGW','NGY','NGX','NHE','NHF','NHI','NHH','NHC']:
  rc=J(E/('NHO_REPLAY_'+prefix+'.json'));assert rc['exit_status']==0
  p=R/rc['result']['unchanged_validator'];b=p.read_bytes();assert b==subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))],cwd=R)
  for n,x in rc['sparse_inputs'].items():assert H(raw(E/x['snapshot']))==x['sha256']
  proven.append(dict(prefix=prefix,validator=str(p.relative_to(R)),validator_sha256=H(b),exit_status=0,checks_removed=0,receipt='NHO_REPLAY_'+prefix+'.json'))
 assert J(R/'evidence/slice-d-finish3-20261106/NHE_L001/receipt.json')['exit_status']==0
 assert J(E/'NHO_L010/receipt.json')['exit_status']==0
 for p in E.glob('NHO_L*/receipt.json'):
  r=J(p);ad=J(E/(p.parent.name+'-admission.json'));assert ad['exit']==0 and ad['reservation']['allowed']is True
  for n,h in r['source_hashes'].items():assert H(raw(p.parent/'sources'/n))==h,(p,n)
 assert len(list(E.glob('NHO_L*/receipt.json')))==len((E/'NHO_ATTEMPTS.jsonl').read_text().splitlines())==40
 # The original caller-domain graph is immutable; explicit callee-specialization facts remain in the selected certificate.
 specialization=next(r for r in l['rows']if r['row']=='TX1:005');assert specialization['NHO_route']=='(y)/(al)'and specialization['NHO_certificate']['packet']['model_root']=='NHH_CMBridge.packet'and specialization['NHO_certificate']['packet']['specialized_child']=='NHH_CMBridge.specialized_packet'
 tests=[]
 for label,i,f in[
  ('inflated closure count',0,lambda x:x['NHO_coverage'].update(CLOSED=336)),
  ('false headline',0,lambda x:x.update(NHO_security_target_established=True)),
  ('false cold replay',0,lambda x:x.update(NHO_cold_release_replay=True)),
  ('tool boundary removed',0,lambda x:next(r for r in x['rows']if r['row']=='TX1:036').update(NHO_boundary='')),
  ('generic function-pointer closure',0,lambda x:next(r for r in x['rows']if r['row']=='TX1:006').update(composed_status='CLOSED')),
  ('root omitted',1,lambda x:x['results'].pop()),
  ('nonstandard raw axiom',1,lambda x:x['results'][0]['walked_axioms'].append('badAxiom')),
  ('fixture omitted',1,lambda x:x['fixtures'].pop()),
  ('fixture axiom erased',1,lambda x:x['fixtures'][0].update(walked_axioms=[])),
  ('walker mismatch',1,lambda x:x['walker_conformance'].update(byte_identical=False)),
  ('nonzero scanner exit',2,lambda x:x.update(exit_status=1)),
  ('dangling reference',2,lambda x:x.update(dangling=1)),
  ('incompatible owner',2,lambda x:x.update(incompatible_owners=1)),
  ('import mismatch',2,lambda x:x.update(import_mismatches=1)),
  ('transcription trust hidden',3,lambda x:next(r for r in x['rows']if r['id']=='ReviewedTranscription-prepared_claim').update(direct_closed_rows=[])),
  ('unaccepted CPI used',3,lambda x:next(r for r in x['rows']if r['id']=='RuntimeCpiReadonlyEntry7').update(used=True)),
  ('trust removed',3,lambda x:x.update(no_trust_removed=False)),
  ('owner conflict suppressed',4,lambda x:x['conflicts'].append({'owner':'bad'}))]:
  vals=[l,a,s,t,c];vals[i]=copy.deepcopy(vals[i]);f(vals[i])
  try:gate(*vals)
  except AssertionError:tests.append(label)
  else:raise AssertionError('accepted mutation '+label)
 assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs'],cwd=R).returncode==0
 for p in E.rglob('*'):
  assert p.name!='__pycache__'
  if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
 for p in E.glob('NHO_*.lean'):assert not re.search(r'^\s*(?:theorem|axiom)\b|\b(?:sorry|admit|native_decide)\b|set_option\s+(?:maxHeartbeats|maxRecDepth)',p.read_text(),re.M),p
 (E/'NHO_VALIDATOR_PROVENANCE.json').write_text(json.dumps(proven,indent=1)+'\n');(E/'NHO_TESTS.json').write_text(json.dumps(dict(status='PASS',rejected=tests),indent=1)+'\n');print(json.dumps(dict(status='PASS',validators=len(proven),mutations_rejected=len(tests),rows=599,CLOSED=335,OPEN=264,roots=a['root_count'],scan_modules=s['modules'])))
