"""Additional refresh gates: no certificate predicate is replaced or weakened."""
from pathlib import Path
import json,lzma,hashlib,copy,collections,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def read(p):
 if p.is_file():return p.read_bytes()
 if Path(str(p)+'.xz').is_file():
  raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(raw)==Path(str(p)+'.sha256').read_text().strip();return raw
 ref=Path(str(p)+'.REFERENCE.json')
 if ref.is_file():
  x=json.loads(ref.read_text());q=E/x['stored_once'];raw=lzma.decompress(q.read_bytes())if x['encoding']=='xz'else q.read_bytes();assert H(raw)==x['sha256'];return raw
 raise FileNotFoundError(p)
def J(p):return json.loads(read(p))
def gate(ledger,audit,scan,trust,ad):
 assert ledger['NGZ_coverage']=={'total':599,'CLOSED':303,'QUALIFIED':0,'OPEN':296}
 assert collections.Counter(r['composed_status']for r in ledger['rows'])=={'CLOSED':303,'OPEN':296}
 assert len({r['row']for r in ledger['rows']})==599
 assert not ledger['NGZ_security_target_established']and not ledger['NGZ_cold_release_replay']
 for rid in ['TX1:036','TX1:040','TX1:041','TX1:043','TX1:044']:
  r=next(x for x in ledger['rows']if x['row']==rid);assert r['composed_status']=='OPEN'and r['NGZ_boundary']=='TOOL-BOUNDARY'
 expected=J(E/'NGZ_AUDIT_ROOTS.json')['roots'];assert audit['root_count']==len(expected)==len(audit['results'])
 assert {x['root']for x in audit['results']}==set(expected)
 for x in audit['results']:assert x['equal']and set(x['walked_axioms'])<={'propext','Quot.sound','Classical.choice'}
 assert audit['status']=='PASS'and not audit['collect_axioms_disagreements']and len(audit['fixtures'])==8
 assert scan['status']=='PASS'and scan['dangling']==scan['incompatible_owners']==scan['import_mismatches']==0
 assert not scan['defects']
 t={r['id']:r for r in trust['rows']};assert t['RuntimeClockSlotBinding']['status']=='ADDED-LEAD'
 assert t['RuntimeCpiReadonlyEntry7']['status']=='ADDED-PENDING-LEAD'and not t['RuntimeCpiReadonlyEntry7']['used']and not t['RuntimeCpiReadonlyEntry7']['direct_closed_rows']
 assert trust['no_trust_removed']
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 return True
if __name__=='__main__':
 ledger=J(E/'NGZ_LEDGER.json');audit=J(E/'NGZ_AUDIT.json');scan=J(E/'NGZ_SCAN.json');trust=J(E/'NGZ_TRUST_USED.json');ad=J(E/'NGZ_L003-admission.json');assert gate(ledger,audit,scan,trust,ad)
 validators=['NFX','NGB','NFT','NFU','NFY','NGE','NGF','NGI','NFV','NGH','NGD','NFW','NGC','NGO','NGM','NGT','NGV','NGN','NGU','NGK','NGP','NGR','NGS','NGA','NGG'];provenance=[]
 for a in validators:
  rc=J(E/('NGZ_REPLAY_'+a+'.json'));assert rc['exit_status']==0,a
  p=R/rc['result']['unchanged_validator'];raw=p.read_bytes()if p.is_file()else subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))],cwd=R)
  for n,x in rc['sparse_inputs'].items():assert H(read(E/x['snapshot']))==x['sha256']
  provenance.append(dict(prefix=a,validator=rc['result']['unchanged_validator'],validator_sha256=H(raw),receipt='NGZ_REPLAY_'+a+'.json',exit_status=0,checks_removed=0))
 tests=[]
 for label,which,change in [
  ('inflated closed count',0,lambda x:x['NGZ_coverage'].update(CLOSED=304)),
  ('false release conclusion',0,lambda x:x.update(NGZ_security_target_established=True)),
  ('cold replay claim',0,lambda x:x.update(NGZ_cold_release_replay=True)),
  ('missing tool boundary',0,lambda x:next(r for r in x['rows']if r['row']=='TX1:036').update(NGZ_boundary='CLOSED')),
  ('missing raw root',1,lambda x:x['results'].pop()),
  ('nonstandard axiom',1,lambda x:x['results'][0]['walked_axioms'].append('badAxiom')),
  ('raw summary disagreement',1,lambda x:x['results'][0].update(equal=False)),
  ('missing fixture',1,lambda x:x['fixtures'].pop()),
  ('dangling reference',2,lambda x:x.update(dangling=1)),
  ('incompatible owner',2,lambda x:x.update(incompatible_owners=1)),
  ('import mismatch',2,lambda x:x.update(import_mismatches=1)),
  ('unaccepted CPI trust used',3,lambda x:next(r for r in x['rows']if r['id']=='RuntimeCpiReadonlyEntry7').update(used=True)),
  ('trust silently removed',3,lambda x:x.update(no_trust_removed=False)),
  ('refused admission',4,lambda x:x['reservation'].update(allowed=False)),
  ('nonzero admission exit',4,lambda x:x.update(exit=78))]:
  values=[ledger,audit,scan,trust,ad];values[which]=copy.deepcopy(values[which]);change(values[which])
  try:gate(*values)
  except AssertionError:tests.append(label)
  else:raise AssertionError('Accepted mutation '+label)
 (E/'NGZ_VALIDATOR_PROVENANCE.json').write_text(json.dumps(provenance,indent=1)+'\n');(E/'NGZ_TESTS.json').write_text(json.dumps(dict(status='PASS',rejected=tests),indent=1)+'\n')
 assert len(list(E.glob('NGZ_L*/receipt.json')))==40
 for p in E.rglob('*'):
  assert p.name!='__pycache__'
  if p.is_file():assert p.stat().st_size<=20_000_000,str(p)
 print(json.dumps(dict(status='PASS',validators=len(validators),mutations_rejected=len(tests),rows=599,CLOSED=303,roots=audit['root_count'],modules=scan['modules'])))
