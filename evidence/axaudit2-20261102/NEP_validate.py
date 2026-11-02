"""Validate receipts, axiom-removal controls, hard failures and pinned cache evidence."""
import hashlib,json,lzma,re,sys,unittest
from pathlib import Path
E=Path(__file__).resolve().parent
STANDARD=['Classical.choice','Quot.sound','propext']
def sha(b):return hashlib.sha256(b).hexdigest()
def rows(attempt,tag):
 return [json.loads(l[len(tag)+1:]) for l in (E/attempt/'stdout.log').read_text().splitlines() if l.startswith(tag+' ')]
def printed(receipt):
 out={}
 for text in receipt['print_axioms']:
  root=text.split("'")[1]
  out[root]=sorted(re.sub(r'\.\{[^}]*\}','',x.strip()) for x in text.split('depends on axioms: [')[1].removesuffix(']').split(',')) if 'depends on axioms: [' in text else []
 return out
def check_result(row,names,axs):
 assert row['equal'] is True
 assert row['walked_axioms']==row['collect_axioms']==axs
 assert len(names)==len(set(names))==row['reachable_constants']
 assert row['root'] in names and set(axs)<=set(names)
 assert row['edges_scanned']>=len(names)-1

def validate(final=True):
 receipts={}
 attempts=[json.loads(l) for l in (E/'NEP_ATTEMPTS.jsonl').read_text().splitlines()]
 scopes=[a for a in attempts if a['event']=='scope']
 assert sum(not a['agg16'] for a in scopes)<=25
 assert sum(a['agg16'] for a in scopes)==(1 if final else 0)
 for p in sorted(E.glob('NEP_*/receipt.json')):
  r=json.loads(p.read_text());a=r['attempt'];receipts[a]=r
  agg=r['command'][4]=='-M15000'
  expected=('15032385536','17179869184') if agg else ('6442450944','8589934592')
  assert (r['limits']['memory.high'],r['limits']['memory.max'])==expected
  assert r['limits']['memory.swap.max']=='0' and r['limits']['pids.max']=='64' and str(r['swaps'])=='0'
  assert r['wall_seconds']>0 and int(r['peak_rss_kib'])>0 and r['source_revision']
  for name,digest in r['source_hashes'].items():assert sha((p.parent/'sources'/name).read_bytes())==digest
  admissions=[a for a in attempts if a['event']=='admission' and a['attempt']==r['attempt']]
  assert admissions and admissions[-1]['exit']==0
  assert json.loads((E/admissions[-1]['receipt']).read_text())['allowed'] is True
 visited=json.loads((E/'NEP_VISITED.json').read_text());decoded={}
 for name,row in visited.items():
  raw=lzma.decompress((E/row['file']).read_bytes());assert sha(raw)==row['sha256']==(E/(name+'.sha256')).read_text().strip()
  names=raw.decode().splitlines();assert len(names)==len(set(names))==row['count'];decoded[name]=names
 for attempt in receipts:
  pr=printed(receipts[attempt])
  for row in rows(attempt,'NEP_RESULT'):
   matches=[n for n in decoded.values() if len(n)==row['reachable_constants'] and row['root'] in n]
   assert matches,(attempt,row['root'])
   check_result(row,matches[0],pr[row['root']])
 fixture=rows('NEP_R024','NEP_RESULT');assert len(fixture)==8
 expected={'matcher':'matchAx','viaPrivate':'privateAx','proof':'proofAx','viaAux':'auxAx'}
 for row in fixture:
  ns,root=row['root'].split('.')
  assert row['walked_axioms']==(['NEP_Planted.'+expected[root]] if ns=='NEP_Planted' else [])
 assert any('matcher.match_1' in n for n in decoded['NEP_fixtures_NEP_Planted.matcher_REACHABLE.txt'])
 assert any(n.startswith('_private.') for n in decoded['NEP_fixtures_NEP_Planted.viaPrivate_REACHABLE.txt'])
 assert any(n.endswith('NEP_Planted.hiddenAux') for n in decoded['NEP_fixtures_NEP_Planted.viaAux_REACHABLE.txt'])
 assert receipts['NEP_R023']['exit_status']==1
 failure=rows('NEP_R023','NEP_FAILURE');assert len(failure)==1
 assert failure[0]['missing']=='AdapterRw.r1_pool_adapter.owned.stage2_owned.match_3'
 assert failure[0]['parent']=='AspisR1.JGx_SdkAfterValidationEq.source' and not failure[0]['complete']
 assert 'PANIC' not in (E/'NEP_R023/stdout.log').read_text()
 pinraw=lzma.decompress((E/'NEP_CACHE_PINS.json.xz').read_bytes());assert sha(pinraw)==(E/'NEP_CACHE_PINS.json.sha256').read_text().strip()
 pins=json.loads(pinraw);assert pins['valid'] and pins['ndr_module_count']==16057
 manifest=(E/'NDR_FINAL_COHORT_PINS.json').read_bytes();assert sha(manifest)==pins['ndr_manifest_sha256']
 pinned={r['path']:r['sha256'] for r in pins['checks'] if r.get('ndr_pin')}
 for row in json.loads(manifest)['entries']:assert pinned[row['module'].replace('.','/')+'.olean']==row['object_sha256']
 output={'schema':'NEP_AXIOMS/v1','complete':False,'scope':'Own axiom-audit script completeness; no security contract changed','fixture_results':fixture,'missing_dependency':failure[0],'cache_verification':{'ndr_modules':16057,'checks':len(pins['checks']),'sha256':sha(pinraw)},'roots':{},'scope_count':len(scopes),'receipts':{a:{k:r[k] for k in ['module','command','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','source_hashes','limits','print_axioms']} for a,r in receipts.items()}}
 if final:
  r=receipts['NEP_R900'];assert r['exit_status']==1
  completed=rows('NEP_R900','NEP_RESULT');failed=rows('NEP_R900','NEP_FAILURE');assert len(completed)==len(failed)==1
  for row in completed:
   assert row['walked_axioms']==STANDARD
   output['roots'][row['root']]={**row,'complete':True}
  for row in failed:
   assert row['missing']==failure[0]['missing']
   output['roots'][row['root']]={**row,'walked_axioms':None,'equal':None,'collect_axioms':printed(r)[row['root']],'status':'hard error; complete raw axiom set unavailable'}
 return output

class NegativeControls(unittest.TestCase):
 def test_missing_axiom_rejected(self):
  row={'equal':True,'walked_axioms':[],'collect_axioms':['A'],'root':'root','reachable_constants':2,'edges_scanned':1}
  with self.assertRaises(AssertionError):check_result(row,['root','A'],['A'])
 def test_truncated_walk_rejected(self):
  row={'equal':True,'walked_axioms':['A'],'collect_axioms':['A'],'root':'root','reachable_constants':3,'edges_scanned':2}
  with self.assertRaises(AssertionError):check_result(row,['root','A'],['A'])
if __name__=='__main__':
 suite=unittest.defaultTestLoader.loadTestsFromTestCase(NegativeControls)
 assert unittest.TextTestRunner().run(suite).wasSuccessful()
 result=validate('--stage-b' not in sys.argv)
 target=E/'NEP_AXIOMS.json';encoded=json.dumps(result,indent=2)+'\n'
 if '--check' in sys.argv:assert target.read_text()==encoded
 elif '--stage-b' not in sys.argv:target.write_text(encoded)
 print(json.dumps({'valid':True,'scope_count':result['scope_count'],'complete':result['complete'],'roots':result['roots']}))
