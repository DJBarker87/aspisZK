"""Strict additive qualification of native tensor windows, controls and sources."""
from pathlib import Path
import hashlib,json,re,subprocess,runpy,sys
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def body(s,name):
 a=s.index('fn '+name+'(');a=s.index('{',a);b=a+1;depth=1
 while depth:depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a+1:b-1]
def inner(s,marker):
 a=s.index(marker);a=s.index('{',a);b=a+1;depth=1
 while depth:depth+=(s[b]=='{')-(s[b]=='}');b+=1
 return s[a+1:b-1]
norm=lambda s:re.sub(r'\s+','',s)
frozen=subprocess.check_output(['git','show','4bb3b3f:crates/aspis-r1-cost-probe/src/weights.rs'],text=True)
frozen_tensor=body(frozen,'tensor');window=inner(frozen_tensor,'for j in (0..n).rev()')
rows=[]
for group in range(59):
 positive=2*group+1 if group<4 else 2*group+2; negative=positive+1
 names=[f'NHI_K{positive:03d}',f'NHI_K{negative:03d}']
 if not all((E/n/'receipt.json').exists()for n in names):raise SystemExit('PENDING '+str(group))
 receipts=[json.loads((E/n/'receipt.json').read_text())for n in names]
 assert receipts[0]['source_hashes']==receipts[1]['source_hashes'],names
 for k,(name,r) in enumerate(zip(names,receipts)):
  assert r['module']==f'weights::NHI_tensor::g{group:02d}'and r['exit_status']==k,(name,'verdict')
  text=(E/name/'stdout.log').read_text();assert ('VERIFICATION:- FAILED'if k else'VERIFICATION:- SUCCESSFUL')in text
  if k:assert 'Failed Checks: assertion failed: good'in text
  assert 'timed out'not in text.lower()
  assert r['limits']==limits and str(r['swaps'])=='0'
  ad=json.loads((E/(name+'-admission.json')).read_text());assert ad['exit']==0 and ad['reservation']['allowed']is True
  graph=json.loads((E/(name+'-graph-check.json')).read_text());lock=json.loads((E/(name+'-lock-check.json')).read_text())
  assert graph['graph_matches_frozen']and not graph['new_package_tuples']and not graph['edge_errors']
  assert lock['unchanged']and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  root=next(z for z in graph['selected_closure']if z['name']=='aspis-r1-cost-probe')
  assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=set(root['features'])
  assert r['env']['CARGO_NET_OFFLINE']=='true'and '-Copt-level=3'in r['env']['RUSTFLAGS']
  assert '--locked'not in r['native_command']and r['native_command'][r['native_command'].index('--harness-timeout')+1]=='90s'
 sys.argv=['NHI_validate',names[0],'kani',f'weights::NHI_tensor::g{group:02d}']
 x=runpy.run_path(str(E/'NHI_native_prepare.py'));code=x['inputs']['crates/aspis-r1-cost-probe/src/NHI_tensor.rs']
 assert hashlib.sha256(code.encode()).hexdigest()==receipts[0]['source_hashes']['NHI_src/crates/aspis-r1-cost-probe/src/NHI_tensor.rs'], 'compiled source version mismatch'
 assert not re.search(r'\bstatic\b|Option\s*<\s*fn\b|stub_verified|proof_for_contract',code)
 actual=body(code,'source_window')
 erased=re.sub(r'product\(x,row\[(\d)\],l\)',r'x.mul(self.factors[k][d][\1])',actual)
 assert norm(erased)==norm(window),'window erasure mismatch'
 if group>=52:
  assert norm(body(code,'source_seed'))=='output[0]=K::ONE;'
  control=body(code,'source_control');erased_control=control.replace('trace[*count]=[d,j,n];*count+=1;',window)
  assert norm(erased_control)==norm(frozen_tensor),'control erasure mismatch'
 rows.append(dict(group=group,positive=names[0],negative=names[1],source_erasure=True,source_sha256=hashlib.sha256(code.encode()).hexdigest()))
assert sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch')=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
failed=json.loads((E/'NHI_K009/receipt.json').read_text());assert failed['exit_status']==1 and 'E0277'in(E/'NHI_K009/stdout.log').read_text()
result=dict(status='PASS NATIVE WINDOWS AND CONTROL ONLY',pairs=59,rows=rows,excluded=['NHI_K009: compile failure before verification','NHI_K120: optional unpaired g59 observation, no credit'],paired_law='AspisR1.LPi_TowerValues.qm_mul; NHI_QProduct.spec',domain='n in {1,4,16}, j<n, arbitrary raw 64-cell prestate and four raw replies; canonical restriction only for Lean product instantiation',field_multiplication_native=False,seed_group=53,control_group=58,quarantined=[],suspended=[],kmx_patch_sha256=sha(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch'))
(E/'NHI_NATIVE_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print('PASS 59 matched pairs; seed and full 21-window control; no native field multiplication')
