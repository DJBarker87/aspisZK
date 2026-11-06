"""Validate against authoritative source inputs, including five rejecting mutations."""
from pathlib import Path
import json,lzma,copy,hashlib,time
from PCE_build_ledger import build,inputs,E,read
STD={'propext','Classical.choice','Quot.sound'}
def validate(ledger):
 assert ledger['source_pins']==inputs(),'input pins changed'
 audit=read(E/'PCE_AUDIT.json');assert audit['status']=='PASS'
 assert len(audit['roots'])==75 and all(set(x['walked_axioms'])<=STD for x in audit['roots']),'nonstandard axiom'
 scan=read(E/'PCE_SCAN.json');assert scan['status']=='PASS' and all(scan[k]==0 for k in ['dangling','duplicate_owners','incompatible_owners','import_defects'])
 assert scan['binary_sha256']==audit['binary_sha256']
 fixtures=audit['fixtures'];assert len(fixtures)==8 and all(r['equal'] and len(r['walked_axioms'])==(1 if i<4 else 0) for i,r in enumerate(fixtures))
 roots=read(E/'PCE_ROOTS.json')['roots'];assert [r['root'] for r in audit['roots']]==roots
 observed=[]
 for i,g in enumerate(read(E/'PCE_GROUPS.json')):
  result=read(E/('PCE_binary_roots'+str(i)+'.json'));assert result['sha256']==audit['binary_sha256'] and result['unchanged'] and result['policy_exit']==0
  assert [r['root'] for r in result['results']]==g
  observed+=result['results']
 assert observed==audit['roots']
 for i in [1,4,5,6,8]+list(range(9,25)):
  rc=read(E/f'PCE_L{i:03d}'/'receipt.json');ad=read(E/f'PCE_L{i:03d}-admission.json')
  assert rc['exit_status']==0 and ad['exit']==0 and ad['reservation']['allowed'] is True
  assert rc['swaps']=='0' or rc['swaps']==0
 composition=read(E/'PCE_COMPOSITION.json');assert not composition['security_target_established']
 nkz=read(E.parent/'pool-inventory2-20261109/NKZ_OBLIGATIONS.json')
 assert {x['name'] for x in composition['sections']}==set(nkz['producers'])
 assert {x['row'] for x in composition['guard_owners']}=={x['row'] for x in nkz['exclusive_guard_owners']}
 expected=build();er={r['id']:r for r in expected['rows']};assert len(ledger['rows'])==397 and {r['id'] for r in ledger['rows']}==set(er)
 for r in ledger['rows']:
  x=er[r['id']]
  assert r['ownership']==x['ownership'],'changed row ownership'
  assert not(r['ownership']=='STREAM-A-SHARED' and r['credited_pool_row']),'shared row credited'
  assert r['status']==x['status'],'status mutation'
  assert r['root']==x['root'],'root mutation'
  assert r['named_hypotheses']==x['named_hypotheses'],'dropped hypothesis'
  assert set(r.get('raw_axioms',[]))<=STD,'nonstandard axiom'
  assert r['exact_statement']==x['exact_statement'],'statement mutation'
  assert r['caller_clauses']==x['caller_clauses'],'caller clause mutation'
  assert r['trust_items_used']==x['trust_items_used'],'trust mutation'
  assert r['privacy_flag']==x['privacy_flag'],'privacy mutation'
  assert r==x,'other row mutation'
 assert ledger==expected,'count/pin/context mutation'
 assert not ledger['security_target_established'],'target inflation'
 return True
def mutate_tests(ledger):
 def rejected(name,change):
  bad=copy.deepcopy(ledger);change(bad)
  try:validate(bad)
  except AssertionError as e:return dict(name=name,rejected=True,reason=str(e))
  raise AssertionError('MUTATION ACCEPTED: '+name)
 idx=next(i for i,r in enumerate(ledger['rows']) if r['credited_pool_row']);shared=next(i for i,r in enumerate(ledger['rows']) if r['ownership']=='STREAM-A-SHARED' and any(r['named_hypotheses']))
 return [rejected('flip status',lambda x:x['rows'][idx].update(status='OPEN')),
 rejected('drop hypothesis',lambda x:x['rows'][shared]['named_hypotheses'][0].pop()),
 rejected('change root',lambda x:x['rows'][idx].update(root='Nat.zero')),
 rejected('add non-standard axiom',lambda x:x['rows'][idx]['raw_axioms'].append('sorryAx')),
 rejected('credit shared row',lambda x:x['rows'][shared].update(credited_pool_row=True))]
if __name__=='__main__':
 start=time.monotonic();p=E/'PCE_LEDGER.json';p=p if p.exists() else E/'PCE_LEDGER.json.xz';x=read(p);validate(x);mut=mutate_tests(x)
 out=dict(status='PASS',exit_status=0,rows=397,new_rows=278,shared_bodies=119,counts=x['counts'],mutation_tests=mut,validator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),ledger_file=p.name,ledger_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),audit_sha256=hashlib.sha256((E/'PCE_AUDIT.json').read_bytes()).hexdigest(),wall_seconds=time.monotonic()-start,scope='Pure receipt/ledger validation; no theorem/native run; target not yet established')
 (E/'PCE_VALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print('PCE validator PASS:397 occurrences and5/5 rejecting mutation tests; target not yet established.')
