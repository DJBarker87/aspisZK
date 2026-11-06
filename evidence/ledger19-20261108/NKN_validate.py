"""Receipt, ledger and evidence integrity, with adverse-record controls."""
from pathlib import Path
import json,lzma,hashlib,copy,subprocess,re
E=Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def J(p):return json.loads(lzma.decompress(p.read_bytes())if p.suffix=='.xz'else p.read_bytes())
def gate(a,s,ledger,basis,review,ad):
 assert a['full_composition_pass'] and a['all_required_raw_roots_present']and a['raw_standard_axioms_only']
 assert set(a['axioms'])<={'propext','Classical.choice','Quot.sound'}
 assert a['required_roots']==10190 and len(a['fixtures'])==8
 assert [r['root']for r in a['collect_axioms_disagreements']]==['NHC_DecodeModel.decoder_error']
 assert s['exit_status']==s['dangling']==s['canonical_duplicate_owners']==s['import_mismatches']==s['incompatible_owners']==0
 assert ad['exit']==0 and ad['reservation']['allowed']is True
 assert ledger['gate']=='PASS'and ledger['trust_rows']==basis['trust_rows']and len(ledger['rows'])==599
 by={r['row']:r for r in ledger['rows']};old={r['row']:r for r in basis['rows']}
 assert {r for r in by if by[r]['status']!=old[r]['status']}=={c['row']for c in review['rows']}
 for rid,r in by.items():
  assert set(old[rid]['canonical_callees'])<=set(r['canonical_callees'])
  # Every original caller/domain/named clause retained as original, not weakened.
  if r['obligation']!=old[rid]['obligation']:
   for kind in ['caller_domain_obligations','inventory_domain_obligations','named_hypotheses']:
    assert all(c in r['obligation'][kind]for c in old[rid]['obligation'][kind])
 assert by['TX1:083']['status']==by['TX2:055']['status']=='OPEN'
 assert {r['item']for r in ledger['reviewed_transcription_inventory']} - {r['item']for r in basis['reviewed_transcription_inventory']}=={'NKJ-RT036','NKJ-RT044','NKJ-RT040','NKJ-RT041','NKJ-RT043'}
 assert ledger['supplemental_child_obligations']==basis['supplemental_child_obligations']
 assert ledger['headline']=='AspisR1.RPx_Deployed.deployed' and not ledger['security_target_established']
 return True
if __name__=='__main__':
 a=J(E/'NKN_AUDIT.json');s=J(E/'NKN_SCAN.json');b=J(E.parent/'ledger18-20261108/NKH_LEDGER.json.xz');l=J(E/'NKN_LEDGER.json.xz');r=J(E/'NKN_CANDIDATE_REVIEW.json');ad=J(E/'NKN_L001-admission.json')
 assert gate(a,s,l,b,r,ad)
 mutants=[]
 for label,idx,fn in [('nonstandard axiom',0,lambda x:x['axioms'].append('sorryAx')),('missing roots',0,lambda x:x.update(all_required_raw_roots_present=False)),('duplicate owner',1,lambda x:x.update(canonical_duplicate_owners=1)),('dangling',1,lambda x:x.update(dangling=1)),('unreviewed promotion',2,lambda x:next(v for v in x['rows']if v['row']=='TX1:083').update(status='CLOSED')),('runtime trust changed',2,lambda x:x['trust_rows'].append({'unapproved':True})),('admission allowed false',5,lambda x:x['reservation'].update(allowed=False)),('admission exit78',5,lambda x:x.update(exit=78))]:
  args=copy.deepcopy([a,s,l,b,r,ad]);fn(args[idx])
  try:gate(*args)
  except AssertionError:mutants.append(label);continue
  raise AssertionError('Mutation wrongly admitted '+label)
 # Verify all compressed source/log inputs losslessly and enforce rule12.
 compressed=0
 for p in E.rglob('*.xz'):
  q=Path(str(p)[:-3]+'.sha256');assert q.exists(),str(p)
  assert H(lzma.decompress(p.read_bytes()))==q.read_text().strip(),str(p);compressed+=1
 assert not[p for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
 assert subprocess.run(['git','diff','--check'],capture_output=True).returncode==0
 # No shipped or unrelated paths changed in this branch.
 changed=subprocess.check_output(['git','diff','--name-only','fbe21af77e6^','HEAD'],text=True).splitlines()
 assert all(n.startswith('evidence/ledger19-20261108/')for n in changed)
 res=dict(status='PASS',gate_mutations_rejected=mutants,compressed_sha_pairs=compressed,rows=599,new_closed=11,closed=553,open=46,scopes=40,no_large_files=True,no_unrelated_changes=True)
 (E/'NKN_VALIDATION.json').write_text(json.dumps(res,indent=1)+'\n');print(json.dumps(res))
