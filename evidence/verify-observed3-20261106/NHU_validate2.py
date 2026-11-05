"""Additive final admission: immutable stage1 checks plus native/model/audit checks."""
from pathlib import Path
import json,hashlib,runpy,re,copy
E=Path(__file__).resolve().parent;R=E.parents[1]
STANDARD={'propext','Classical.choice','Quot.sound'}
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
def read(n):return json.loads((E/n).read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def receipt(a):return read(a+'/receipt.json')
def standard(line):
 assert 'sorryAx'not in line and ('does not depend on any axioms' in line or 'depends on axioms:'in line),line
 if 'depends on axioms:'in line:
  names=line.split('[',1)[1].split(']',1)[0];assert {x.strip() for x in names.split(',') if x.strip()}<=STANDARD,line

def validate(packet=None):
 sealed=runpy.run_path(str(E/'NHU_VALIDATE_STAGE1.py'))['validate']();assert sealed['status']=='PASS'
 spec=read('NHU_CANDIDATE.json');assert sha(E/'NHU_CANDIDATE.json')==SPEC_SHA
 p=read('NHU_CLOSED.json') if packet is None else packet
 assert p==spec,'Candidate schema/domain/premise/modifies cannot be broadened'
 rows=[row for f in p['functions'] for row in f['rows']]
 assert rows==['TX1:071','TX1:073','TX1:074','TX1:075','TX1:076','TX1:130','TX1:230','TX1:243','TX1:248','TX1:322','TX1:326']
 assert not p['root137_closed'] and not p['finish136_closed'] and not p['prepare_op9_instantiated']
 assert p['frozen_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
 edges=read('NHU_EDGES.json');assert sha(E/'NHU_EDGES.json')==EDGES_SHA
 assert len(edges['closed_edges'])==10 and all(e['caller'] in rows for e in edges['closed_edges'])
 assert not edges['root137_closed'] and not edges['finish136_closed'] and not edges['prepare_op9_instantiated']
 assert sha(E/'NHU_KMX.patch')==KMX
 shipped=read('NHU_SHIPPED_SOURCE.json');assert shipped['status']=='PASS'
 assert all(shipped[n]['frozen']==shipped[n]['current'] and not shipped[n]['dirty'] for n in ['crates','programs'])
 attempts=[json.loads(l) for l in (E/'NHU_ATTEMPTS.jsonl').read_text().splitlines()]
 assert len({a['attempt'] for a in attempts})==len(attempts)
 kinds={k:sum(a['kind']==k for a in attempts) for k in {a['kind'] for a in attempts}}
 assert kinds['kani']==80 and sum(a['kind']!='kani' for a in attempts)<=90
 assert not any(a['kind']=='extract' for a in attempts)
 # Every run, including own input errors and diagnostics, had admission and a frozen graph/lock check.
 for a in attempts:
  ad=read(a['attempt']+'-admission.json');assert ad['exit']==0 and ad['reservation']['allowed'] is True
  rc=receipt(a['attempt']);assert rc['exit_status']==a['exit_status']
  config=read(a['attempt']+'.json');assert config['timeout']==180
  assert all(k in rc for k in ['wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms'])
  assert rc['swaps']=='0'
  assert rc['deps_fingerprint']['selected_objects']
  if a['kind']=='kani':
   env=config['env'];assert env['CARGO_NET_OFFLINE']=='true' and env['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
   assert env['RUSTFLAGS'].startswith('-Copt-level=3') and '--locked'not in config['native_command']
   assert config['native_command'][config['native_command'].index('--harness-timeout')+1]=='90s'
   graph=read(a['attempt']+'-graph-check.json');lock=read(a['attempt']+'-lock-check.json');source=read(a['attempt']+'-source-check.json')
   assert graph['graph_matches_frozen'] and not graph['edge_errors'] and not graph['new_package_tuples']
   assert graph['lock_sha256']==LOCK and lock==dict(before=LOCK,after=LOCK,unchanged=True)
   assert not source['errors']
  # Immutable content-addressed snapshots include every source used by validation/proofs.
  for name,h in rc['source_hashes'].items():
   path=E/a['attempt']/'sources'/name
   assert path.is_file() and sha(path)==h,(a['attempt'],name)
 # Primary native packets and their exact same-source inverse controls.
 pairs=[]
 for f in p['functions']:
  assert f['status']=='CLOSED' and not f['inner_hypotheses_remaining']
  for pos,neg in f.get('native_pairs',[]):
   rp,rn=receipt(pos),receipt(neg);cp,cn=read(pos+'.json'),read(neg+'.json')
   lp,ln=(E/pos/'stdout.log').read_text(),(E/neg/'stdout.log').read_text()
   assert rp['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in lp
   assert rn['exit_status']==1 and 'VERIFICATION:- FAILED' in ln and 'Failed Checks:'in ln
   assert not any(s in ln.lower() for s in ['timed out','unwinding assertion','excessive memory','memory exhausted'])
   assert rp['source_hashes']==rn['source_hashes'] and cp['module']==cn['module']
   assert cp['native_command']==cn['native_command']
   e1,e2=cp['env'].copy(),cn['env'].copy();flags1=e1.pop('RUSTFLAGS');flags2=e2.pop('RUSTFLAGS');assert e1==e2
   assert flags2.startswith(flags1+' --cfg NHU_') and len(flags2.split('--cfg'))==len(flags1.split('--cfg'))+1
   if int(pos[-3:]) in [31,35,37]:assert 'Failed Checks: |result|'in ln
   pairs.append([pos,neg])
 modules=read('NHU_MODULES.json');assert len(modules)==39
 for row in modules:
  rc=receipt(row['attempt']);assert rc['kind']=='lean' and rc['exit_status']==0
  assert sha(E/(row['module']+'.lean'))==row['sha256']==rc['source_hashes']['NHU_generated/'+row['module']+'.lean']
  assert rc['print_axioms'];[standard(l) for l in rc['print_axioms']]
 joint=receipt('NHU_L075');assert joint['exit_status']==0
 assert joint['source_hashes']['NHU_generated/NHU_COMBINED_IMPORT.lean']==sha(E/'NHU_COMBINED_IMPORT.lean')
 assert 'import NGK_COMBINED_IMPORT' in (E/'NHU_COMBINED_IMPORT.lean').read_text()
 assert any("'AspisR1.RPx_Deployed.deployed'"in l for l in joint['print_axioms'])
 [standard(l) for l in joint['print_axioms']]
 groups=read('NHU_AUDIT_ROOTS.json')['groups'];assert len(groups)==8
 results=[]
 for i in range(1,8):
  a=f'NHU_L{75+i:03}';rc=receipt(a);raw=read(f'NHU_audit/batch{i}/proof{i}.json')
  assert rc['exit_status']==raw['exit_status']==0
  assert [r['root'] for r in raw['results']]==groups[i]
  for r in raw['results']:
   assert r['equal'] and set(r['walked_axioms'])==set(r['collect_axioms']) and set(r['walked_axioms'])<=STANDARD
  results.extend(raw['results'])
 assert len(results)==79 and len({r['root'] for r in results})==79
 scan=[json.loads(l) for l in (E/'NHU_LOADED_scan.jsonl').read_text().splitlines()]
 assert receipt('NHU_L083')['exit_status']==0 and len(scan)==13832
 assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in scan)
 assert read('NHU_DRIVER_REUSE.json')['status']=='PASS' and receipt('NHU_L021')['exit_status']==0
 assert len(read('NHU_audit/fixtures/fixtures.json')['results'])==8
 export=read('NHU_EXPORT.json');assert export['status']=='PASS' and receipt('NHU_L084')['exit_status']==0
 assert len(export['modules'])==40 and export['closure_modules']==13832 and not export['cache_deleted']
 assert sha(E/'NHU_CLOSURE_PINS.json')==export['closure_sha256']==(E/'NHU_CLOSURE_PINS.json.sha256').read_text().strip()
 assert not any('XRn_'in (E/(m['module']+'.lean')).read_text() for m in modules)
 return dict(status='PASS',new_rows=rows,inherited_NHG_rows=18,baseline='sealed original stage1 plus NHG_final_validate read-only',checks_added_only=True,root137_closed=False,finish136_closed=False,prepare_op9_instantiated=False,new_raw_roots=79,sealed_stage1_raw_roots=6,scan_modules=13832,kinds=kinds,charged_lean_support=sum(a['kind']!='kani' for a in attempts),native_pairs=pairs,trust_added=[],trust_removed=[],reclassification='P6/D188 option A retained')

EDGES_SHA='868613f4aa613f5eca9dd81aa6feac65a7ca0e64689288918beb2784bddbe790'
SPEC_SHA='fa0e596b5fba8061ade84faab1d747ac47d5e97ff5990434297d7975e6158eae'
if __name__=='__main__':
 p=read('NHU_CANDIDATE.json');result=validate(p);denials=[]
 mutations=[('promote root',lambda d:d.update(root137_closed=True)),('promote finish',lambda d:d.update(finish136_closed=True)),('instantiate op9',lambda d:d.update(prepare_op9_instantiated=True)),('broaden tower',lambda d:d['functions'][2].update(domain='every coordinate')),('drop domain',lambda d:d['functions'][0].update(domain='')),('success premise',lambda d:d['functions'][4].update(inner_hypotheses_remaining=['claims succeeds'])),('wrong row',lambda d:d['functions'][0].update(rows=['TX1:137'])),('allow outside writes',lambda d:d['functions'][6].update(modifies='arbitrary caller state')),('unpaired native',lambda d:d['functions'][0].update(native_pairs=[])),('wrong model root',lambda d:d['functions'][0].update(lean_root='AspisR1.RPx_Deployed.deployed')),('change target',lambda d:d.update(headline='AspisR1.toy')),('change source',lambda d:d.update(frozen_revision='HEAD'))]
 for name,edit in mutations:
  bad=copy.deepcopy(p);edit(bad)
  try:validate(bad)
  except AssertionError:denials.append(dict(name=name,rejected=True))
  else:raise AssertionError('mutation admitted: '+name)
 (E/'NHU_CLOSED.json').write_text(json.dumps(p,indent=1)+'\n')
 (E/'NHU_LEDGER_DELTA.json').write_text(json.dumps(result,indent=1)+'\n')
 (E/'NHU_ADMISSION2_DENIALS.json').write_text(json.dumps(denials,indent=1)+'\n')
 (E/'NHU_AUDIT.json').write_text(json.dumps(dict(status='PASS',joint='NHU_L075',raw=[f'NHU_L{i:03}' for i in range(76,83)],scan='NHU_L083',export='NHU_L084',new_roots=79,source_modules=39,scan_modules=13832,standard_axioms=sorted(STANDARD),calibration='NHU_L021;8 exact fixtures',denial_controls=len(denials),headline='AspisR1.RPx_Deployed.deployed',headline_standard_axioms=True,target_established=False),indent=1)+'\n')
 print(json.dumps({k:v for k,v in result.items() if k!='native_pairs'}))
