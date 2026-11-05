"""Additive NIH admission; inherited NHU validator is invoked read-only."""
from pathlib import Path
import json,hashlib,re,runpy,copy,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1]
STD={'propext','Classical.choice','Quot.sound'};LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read(n):return json.loads((E/n).read_text())
def rc(a):return read(a+'/receipt.json')
def standard(line):
 assert 'sorryAx'not in line,line
 if 'does not depend on any axioms'in line:return
 assert 'depends on axioms:'in line,line
 assert {x.strip() for x in line.split('[',1)[1].split(']',1)[0].split(',') if x.strip()}<=STD,line

def validate(candidate=None):
 inherited=runpy.run_path(str(E.parent/'verify-observed3-20261106/NHU_validate2.py'))['validate']()
 assert inherited['status']=='PASS'
 spec=read('NIH_CANDIDATE.json');p=spec if candidate is None else candidate
 assert p==spec,'Sealed function/domain/pair/root/modifies carrier cannot be broadened'
 assert [x['rows'][0] for x in p['functions']]==[f'TX1:{n:03}'for n in [210,211,212,213,221,222,226,264,309,311,312,313,314,315,316,317,318,319,320,325]]
 assert p['frozen_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 assert p['headline']=='AspisR1.RPx_Deployed.deployed'
 assert not p['root137_closed'] and not p['finish136_closed'] and not p['prepare_op9_instantiated']
 assert read('NIH_SHIPPED_SOURCE.json')['status']=='PASS'
 assert read('NIH_WALKER_PINS.json')['walker_byte_identical']
 attempts=[json.loads(l) for l in (E/'NIH_ATTEMPTS.jsonl').read_text().splitlines()]
 assert len({x['attempt'] for x in attempts})==len(attempts)
 assert sum(x['kind']=='kani'for x in attempts)==100
 assert sum(x['attempt'].startswith('NIH_L')for x in attempts)==90
 assert sum(x['kind']=='extract'for x in attempts)==1 and rc('NIH_E001')['exit_status']==101
 for x in attempts:
  a=x['attempt'];r=rc(a);ad=read(a+'-admission.json')
  assert ad['exit']==0 and ad['reservation']['allowed'] is True,a
  assert r['exit_status']==x['exit_status'],a
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},a
  assert r['swaps']=='0' and all(k in r for k in ['module','command','wall_seconds','peak_rss_kib','source_revision','source_hashes','print_axioms']),a
  if x['kind']=='kani':
   cfg=read(a+'.json');gate='NIH_K009' if a=='NIH_K010' else a
   if a=='NIH_K010':assert rc(a)['exit_status']==101 and 'NIH_K009.json' in cfg['command']
   g=read(gate+'-graph-check.json');lock=read(gate+'-lock-check.json')
   assert cfg['env']['CARGO_NET_OFFLINE']=='true' and cfg['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3',a
   if 'cargo-kani'in cfg['native_command'][0]:assert '--locked'not in cfg['native_command'],a
   assert g['graph_matches_frozen'] and not g['edge_errors'] and not g['new_package_tuples'],a
   assert g['lock_sha256']==LOCK and lock['before']==LOCK and lock['after']==LOCK and lock['unchanged'],a
   assert not read(gate+'-source-check.json')['errors'],a
 for f in p['functions']:
  assert f['complete_carrier'] and f['root_domain'] and 'RECLASSIFICATION'in f['trust']
  for pos,neg in f['native_pairs']:
   for a,status,word in [(pos,0,'VERIFICATION:- SUCCESSFUL'),(neg,1,'VERIFICATION:- FAILED')]:
    assert rc(a)['exit_status']==status,a
    assert word in (E/a/'stdout.log').read_text(),a
   # Every introduced source is pinned to the actual submitted snapshot.
   assert rc(pos)['source_hashes'] and rc(neg)['source_hashes']
   assert 'NHU_invert'in read(neg+'.json')['env']['RUSTFLAGS'] or 'NIH_invert'in read(neg+'.json')['env']['RUSTFLAGS']
 # The live/exhausted invariant finding cannot be hidden by a partial packet.
 expand=next(f for f in p['functions'] if f['rows']==['TX1:212'])
 assert ['NIH_K095','NIH_K096']in expand['native_pairs']
 internal=next(f for f in p['functions'] if f['rows']==['TX1:319'])
 assert ['NIH_K097','NIH_K098']in internal['native_pairs']
 assert read('NIH_OUTER_DOMAIN_REPAIR.json')['no_success_premise']
 # No old static packed-native receipt is used as a passing certificate.
 assert all(not a.startswith(('NDN_K','NDE_K')) for f in p['functions']for pair in f['native_pairs']for a in pair)
 modules=read('NIH_MODULES.json');allroots=[]
 for m in modules:
  assert sha(E/(m['module']+'.lean'))==m['sha256']
  r=rc(m['attempt']);assert r['exit_status']==0 and r['source_hashes']['NIH_generated/'+m['module']+'.lean']==m['sha256']
  for line in r['print_axioms']:standard(line)
  allroots.extend(re.match("'([^']+)'",line)[1] for line in r['print_axioms'])
 roots=read('NIH_AUDIT_ROOTS.json')['groups'];assert [s for g in roots for s in g]==allroots
 assert all(s in allroots for f in p['functions'] for s in f['lean_roots'])
 combined=rc('NIH_L081');assert combined['exit_status']==0
 assert (E/'NIH_COMBINED_IMPORT.lean').read_text().startswith('import NGK_COMBINED_IMPORT\n')
 for line in combined['print_axioms']:standard(line)
 fixtures=read('NIH_audit/fixtures/fixtures.json')['results']
 expected=json.loads((E.parent/'verify-observed3-20261106/NHU_audit/fixtures/fixtures.json').read_text())['results']
 assert len(fixtures)==8
 assert [(r['root'],r['walked_axioms'],r['collect_axioms'],r['equal'])for r in fixtures]==[(r['root'],r['walked_axioms'],r['collect_axioms'],r['equal'])for r in expected]
 audited=[]
 for i,group in enumerate(roots):
  r=read(f'NIH_audit/batch{i}/proof{i}.json');assert r['exit_status']==0
  for x in r['results']:
   assert x['equal'] and set(x['walked_axioms'])<=STD and set(x['collect_axioms'])<=STD,x['root']
   audited.append(x['root'])
 assert audited==allroots
 assert read('NIH_audit/scan/scan.json')['exit_status']==0
 loaded=[json.loads(l) for l in (E/'NIH_LOADED_scan.jsonl').read_text().splitlines()]
 assert loaded and all(not x['dangling'] and x['imports_match'] and not x['duplicate_owners'] for x in loaded)
 export=read('NIH_EXPORT.json');assert export['status']=='PASS' and export['closure_modules']==len(loaded) and not export['cache_deleted']
 assert sha(E/'NIH_CLOSURE_PINS.json')==export['closure_sha256']
 assert all(m['module']in export['modules'] for m in modules)
 # Final deliverable consistency is additive to the certificate checks above.
 if (E/'NIH_CLOSED.json').exists():
  closed=read('NIH_CLOSED.json');assert all(closed[k]==p[k] for k in p)
  cone=read('NIH_CONE.json');rows={r['row']:r for r in cone['rows']}
  assert all(rows[r]['status']=='CLOSED (NIH)' for f in p['functions']for r in f['rows'])
  assert rows['TX1:147']['status']=='CLOSED (import NGO)'
  assert not rows['TX1:136']['status'].startswith('CLOSED') and not rows['TX1:137']['status'].startswith('CLOSED')
  assert cone['counts']=={'rows':168,'closed':120,'open':48}
  delta=read('NIH_LEDGER_DELTA.json');assert delta['added_closed_rows']==[f['rows'][0] for f in p['functions']] and not delta['checks_removed']
  assert not delta['root137_closed'] and not delta['finish136_closed'] and not delta['prepare_op9_instantiated']
  assert read('NIH_CLEANUP.json')['own_cache_deleted'] is False
 return dict(status='PASS',rows=20,roots=len(allroots),modules=len(modules),scanned_modules=len(loaded),kani=100,lean_support=90,extraction=1,root137_closed=False,finish136_closed=False,prepare_op9_instantiated=False,inherited=inherited['status'])
if __name__=='__main__':
 result=validate();denials=[];original=read('NIH_CANDIDATE.json')
 for key in ['root137_closed','finish136_closed','prepare_op9_instantiated']:
  bad=copy.deepcopy(original);bad[key]=True
  try:validate(bad)
  except AssertionError:denials.append(key)
  else:raise AssertionError('unrejected promotion '+key)
 for key in ['root_domain','native_pairs','lean_roots','complete_carrier','trust']:
  bad=copy.deepcopy(original);bad['functions'][0][key]='broadened/removed'
  try:validate(bad)
  except AssertionError:denials.append(key)
  else:raise AssertionError('unrejected mutation '+key)
 result['denial_controls']=denials
 (E/'NIH_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
