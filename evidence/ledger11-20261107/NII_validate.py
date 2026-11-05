"""Independent additive checks: evidence mutations cannot turn the failed full gate into a pass."""
from pathlib import Path
import json,lzma,hashlib,copy,subprocess,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):
 p=Path(p);p=p if p.is_absolute()else E/p
 if p.exists():return json.loads(p.read_bytes())
 raw=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(raw)==Path(str(p)+'.sha256').read_text().strip();return json.loads(raw)
def evidence(p):
 p=Path(p)
 if p.exists():return p.read_bytes()
 x=J(str(p)+'.REFERENCE.json');raw=(E/x['stored_once']).read_bytes();raw=lzma.decompress(raw)if x['encoding']=='xz'else raw;assert H(raw)==x['sha256'];return raw
BASE=J(R/'evidence/ledger10-20261106/NHO_LEDGER.json');DELTA=J('NII_COUNT_RECONCILIATION.json');CONFLICT=J('NII_CONFLICTS.json')
def ledger_check(x):
 assert len(x['rows'])==599 and len({r['row']for r in x['rows']})==599
 prior={r['row']:r for r in BASE['rows']};new={r['row']:r for r in x['rows']};added={r for d in DELTA['deltas']for r in d['new_closed_rows']};q=set(CONFLICT['qualified_rows']);assert len(added)==58 and len(q)==14
 for rid,r in new.items():
  before=prior[rid]
  for k,v in before.items():
   if k!='composed_status':assert r[k]==v,(rid,k)
  expected='QUALIFIED'if rid in q else'CLOSED'if rid in added else before['composed_status']
  assert r['composed_status']==expected,(rid,expected)
  assert r['NII_source_validator_status']==('CLOSED'if rid in added else before['composed_status'])
  if rid in added:
   c=r['NII_certificate'];p=R/c['path'];assert H(p.read_bytes())==c['sha256']
   assert not c['packet'].get('inner_hypotheses_remaining',[])
  if rid in q:assert r['NII_provider']=='NHJ'and r['NII_qualification']
 assert x['NII_coverage']==dict(total=599,CLOSED=379,QUALIFIED=14,OPEN=206)
 assert x['NII_source_validator_coverage']==dict(total=599,CLOSED=393,QUALIFIED=0,OPEN=206)
 assert x['NII_headline']=='AspisR1.RPx_Deployed.deployed'and not x['NII_security_target_established']and not x['NII_cold_release_replay']
 t={t['id']:t for t in x['trust_rows']};oldtrust={t['id']:t for t in BASE['trust_rows']}
 assert set(oldtrust)<=set(t)and all(t[n]['status']==v['status']for n,v in oldtrust.items())
 assert not any(n.startswith(('NIB-P','NHY_','NHD_'))for n in t)
 assert t['RuntimeCpiReadonlyEntry7']['used']is False and not t['RuntimeCpiReadonlyEntry7']['direct_closed_rows']
 for n in ['RuntimeClockSlotBinding','RuntimeReturnDataClear','ReviewedTranscription-prepared_claim','ReviewedTranscription-queries_from_pairs']:assert t[n]['status']=='ADDED-LEAD'and t[n]['use_sites']
 assert new['TX1:006']['NII_route']=='(al)'and new['TX1:006']['NII_certificate']['packet']['instantiations']==['M31::inv']
 assert new['TX1:130']['NII_route']=='(ae) reclassification (z)(1)'
 for rid in ['TX1:036','TX1:040','TX1:041','TX1:043','TX1:044']:assert new[rid]['composed_status']=='OPEN'and new[rid]['NII_boundary']=='TOOL-BOUNDARY'
def run(final=False):
 x=J('NII_LEDGER.json');ledger_check(x);denied=[]
 for label,mutate in [
 ('qualified NHJ promotion',lambda z:z['rows'][next(i for i,r in enumerate(z['rows'])if r['row']=='TX1:331')].update(composed_status='CLOSED')),
 ('frozen body drift',lambda z:z['rows'][0].update(frozen_body_sha256='0'*64)),
 ('canonical edge drift',lambda z:z['rows'][0]['canonical_callees'].append('invented')),
 ('source union count drift',lambda z:z['NII_source_validator_coverage'].update(CLOSED=394)),
 ('qualified count suppression',lambda z:z['NII_coverage'].update(QUALIFIED=0)),
 ('pending trust use',lambda z:next(t for t in z['trust_rows']if t['id']=='RuntimeCpiReadonlyEntry7').update(used=True)),
 ('target promotion',lambda z:z.update(NII_security_target_established=True)),
 ('missing row',lambda z:z['rows'].pop()),
 ('generic inv promotion',lambda z:next(r for r in z['rows']if r['row']=='TX1:006')['NII_certificate']['packet'].update(instantiations=['arbitrary fn']))]:
  z=copy.deepcopy(x);mutate(z)
  try:ledger_check(z)
  except (AssertionError,KeyError):denied.append(label)
  else:raise AssertionError('Accepted evidence mutation: '+label)
 jobs=J('NII_VALIDATOR_JOBS.json')
 for a,path in jobs.items():
  rc=J('NII_REPLAY_'+a+'.json');assert rc['exit_status']==0 and rc['result']['unchanged_validator']=='evidence/'+path
  p=R/'evidence'/path;raw=p.read_bytes();assert raw==subprocess.check_output(['git','show','HEAD:evidence/'+path],cwd=R)
  assert H((E/'NII_replay.py').read_bytes())==rc['source_sha256']
  for original,pin in rc['sparse_inputs'].items():assert H((E/pin['snapshot']).read_bytes())==pin['sha256'],original
 for r in J('NII_READONLY_PROVENANCE.json'):
  if r.get('snapshot'):assert H((E/r['snapshot']).read_bytes())==r['sha256']
 assert CONFLICT['status']=='FINDING'and not CONFLICT['owner_patched']and not CONFLICT['forest_changed']
 for a in ['NII_L001','NII_L002']:
  rc=J(a+'/receipt.json');assert rc['exit_status']==1 and CONFLICT['declaration']in(E/a/'stdout.log').read_text()
 if final:
  receipts=[J(p/'receipt.json')for p in sorted(E.glob('NII_L[0-9][0-9][0-9]'))];assert len(receipts)==40
  for rc in receipts:
   ad=J(rc['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed']is True
   assert rc['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}and int(rc['swaps'])==0
   assert rc['exit_status']not in [124,137]
   for path,h in rc['source_hashes'].items():assert H(evidence(E/rc['attempt']/'sources'/path))==h
  audit=J('NII_AUDIT.json');scan=J('NII_SCAN.json');assert audit['status']=='FULL_COMPOSITION_FAILED_OWNER_CONFLICT'and not audit['full_composition_pass']
  assert audit['diagnostic_raw_standard_only']and audit['diagnostic_root_count']==len(J('NII_AUDIT_ROOTS.json')['roots'])
  assert len(audit['fixtures'])==8 and all(r['equal']for r in audit['fixtures'])
  assert scan['status']=='FULL_GATE_BLOCKED_OWNER_CONFLICT'and scan['diagnostic']['exit_status']==0 and not scan['full_gate_pass']
  assert all(scan['diagnostic'][k]==0 for k in ['dangling','incompatible_owners','import_mismatches'])
 result=dict(status='PASS',checks_added_only=True,unchanged_validators=len(jobs),mutation_denials=denied,headline_gate='FAIL owner conflict; never reclassified as pass',final=final)
 (E/'NII_TESTS.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
if __name__=='__main__':run('--final'in sys.argv)
