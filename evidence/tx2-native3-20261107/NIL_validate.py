"""NID baseline admission/resource/lock/feature checks plus NIL evidence guards."""
from pathlib import Path
import importlib.util,hashlib,json,sys,re,subprocess
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;ROOT=E.parents[1]
spec=importlib.util.spec_from_file_location('NIL_BaseValidation',E/'NIL_BaseValidation.py');base=importlib.util.module_from_spec(spec);spec.loader.exec_module(base)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def receipts():return [json.loads(p.read_text()) for p in sorted(E.glob('NIL_[KLE][0-9][0-9][0-9]/receipt.json'))]
def validate(final=False):
 rs=receipts();counts={'kani':0,'extract':0,'lean_support':0}
 for r in rs:
  a=r['attempt'];ad=json.loads((E/(a+'-admission.json')).read_text())
  assert ad['exit']==0 and ad['reservation']['allowed'] is True,('admission',a)
  assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},('limits',a)
  assert r['source_revision'] and r['wall_seconds']>=0 and int(r['peak_rss_kib'])>0 and str(r['swaps'])=='0'
  for n,h in r['source_hashes'].items():assert sha(E/a/'sources'/n)==h,(a,n)
  kind=r['kind'];counts[kind if kind in ['kani','extract'] else 'lean_support']+=1
  if kind=='kani':base.check(ad,r,json.loads((E/(a+'-graph-check.json')).read_text()),json.loads((E/(a+'-lock-check.json')).read_text()))
 assert counts['kani']<=120 and counts['extract']<=1 and counts['lean_support']<=80,counts
 for pin in json.loads((E/'NIL_INPUT_PINS.json').read_text())['inputs']:assert sha(ROOT/pin['path'])==pin['sha256'],pin['path']
 assert sha(ROOT/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert subprocess.run(['git','diff','--quiet','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','HEAD','--','crates','programs'],cwd=ROOT).returncode==0
 assert not subprocess.check_output(['git','status','--porcelain','--','crates','programs'],cwd=ROOT,text=True).strip(),'shipped working tree modified'
 for matrix in ['NIL_NATIVE_MATRIX.json','NIL_TREE_MATRIX.json','NIL_PREFIX_MATRIX.json','NIL_EXTRA_MATRIX.json','NIL_HEADER_MATRIX.json']:
  if not (E/matrix).exists():continue
  for row in json.loads((E/matrix).read_text()):
   if not row.get('status','').startswith('qualified'):continue
   for mode in ['positive','control','rename']:
    a=row[mode];r=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
    if mode=='control':
     assert r['exit_status']!=0 and 'VERIFICATION:- FAILED' in out and 'unwinding assertion' not in out.lower()
     assert 'Failed Checks: assertion failed:' in out or 'core::panicking::assert_failed_inner' in out
    else:assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in out
    flags=r['env']['RUSTFLAGS'];assert (' --cfg NIL_invert' in flags)==(mode=='control')
   source_rows=[json.loads((E/row[m]/'receipt.json').read_text())['source_hashes'] for m in ['positive','control','rename']]
   if row['family']=='tree0_facet0':
    assert source_rows[1]==source_rows[2]
    assert {k for k in source_rows[0] if source_rows[0][k]!=source_rows[1].get(k)}=={'NIL_SOURCE_PINS.json','NIL_src/crates/aspis-r1-cost-probe/src/NIL_tree_native.rs'}
    import runpy
    assert runpy.run_path(str(E/'NIL_control_erasure.py'))['x']['status']=='PASS'
   else:assert source_rows[0]==source_rows[1]==source_rows[2],row['family']
 if (E/'NIL_CTOR_PLAN.json').exists():
  row=json.loads((E/'NIL_CTOR_PLAN.json').read_text())
  if row.get('status','').startswith('qualified'):
   sources=[]
   for mode,flag in [('positive',None),('control_value','NIL_bad_box_value'),('control_allocation','NIL_bad_alloc'),('rename_attempt',None)]:
    r=json.loads((E/row[mode]/'receipt.json').read_text());out=(E/row[mode]/'stdout.log').read_text();sources.append(r['source_hashes'])
    assert (' --cfg '+flag in r['env']['RUSTFLAGS']) if flag else not any(f in r['env']['RUSTFLAGS'] for f in ['NIL_bad_box_value','NIL_bad_alloc'])
    if flag:assert r['exit_status']!=0 and 'VERIFICATION:- FAILED' in out and 'unwinding assertion' not in out.lower() and ('assertion' in out.lower() or 'core::panicking::assert_failed_inner' in out)
    else:assert r['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in out
   assert sources[0]==sources[1]==sources[2]==sources[3]
 if final:
  assert json.loads((E/'NIL_CLOSED.json').read_text())['new_composed_rows']==0
  d=json.loads((E/'NIL_LEDGER_DELTA.json').read_text());assert d['row']=='TX2:065' and d['after']=='OPEN' and d['promotions']==[]
  assert json.loads((E/'NIL_AUDIT.json').read_text())['status']=='PASS'
  assert json.loads((E/'NIL_SCAN.json').read_text())['status']=='PASS'
  mods=json.loads((E/'NIL_MODULES.json').read_text())
  for row in mods['selected']:
   r=json.loads((E/row['attempt']/'receipt.json').read_text());assert r['exit_status']==0
   assert sha(E/(row['module']+'.lean'))==r['source_hashes']['NIL_generated/'+row['module']+'.lean']
   assert all('sorryAx' not in line for line in r['print_axioms'])
  assert json.loads((E/'NIL_VALIDATOR_CONTROLS.json').read_text())['status']=='PASS'
 for p in E.rglob('*'):
  if p.is_file():assert p.stat().st_size<=20*1024**2,('oversize',str(p))
 return {'status':'PASS','counts':counts,'final':final,'promoted_rows':0,'receipts':len(rs)}
if __name__=='__main__':
 out=validate('--final' in sys.argv);(E/'NIL_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
