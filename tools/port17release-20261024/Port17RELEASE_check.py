#!/usr/bin/env python3
"""Source/receipt audit only. Does not replay Lean or any frozen manifest."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/port17release-20261024';L=R/'docs/research/100bit-spend-path-20261013/lean';T=R/'tools/port17release-20261024'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
configs=sorted(T.glob('lean-*.json'));assert len(configs)<=26
inv=json.loads((E/'dependency-inventory.json').read_text());assert inv['all_selected_cache_match'] and not inv['source_obstructions']
for n,x in inv['selected'].items():
 if 'source_path' in x:
  p=E/'dependency-source'/(n.replace('.','/')+'.lean');assert sha(p)==x['source_sha256'],n
local_manifest=Path('/tmp/port17release-local-dependencies.json')
if local_manifest.exists():
 for name,row in json.loads(local_manifest.read_text()).items():
  assert sha(Path(row['path']))==row['sha256'],('frozen local import changed',name)
accepted={};failed=[]
for c in configs:
 cfg=json.loads(c.read_text());a=cfg['attempt'];p=E/a/'receipt.json'
 if not p.exists():
  assert a=='lean-011';failed.append({'attempt':a,'stage':'pre-Lean guard','reason':'environment-sensitive guard fixed; charged'});continue
 r=json.loads(p.read_text())
 if r['exit_status']!=0:failed.append({'attempt':a,'exit':r['exit_status']});continue
 for n,h in r['source_hashes'].items():assert sha(E/a/'sources'/n)==h,(a,n)
 for line in r['print_axioms']:
  if 'does not depend on any axioms' in line:continue
  ax=re.search(r'depends on axioms:\s*\[([^]]*)\]',line,re.S);assert ax,line
  names=[re.sub(r'\.\{[^}]*\}','',s.strip()) for s in ax[1].split(',')]
  assert set(names)<={'propext','Classical.choice','Quot.sound'},(a,line)
 assert str(r['swaps'])=='0',a
 if 'limits' in r:assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 else:assert r['aggregate_child_peak_rss_bytes']<8*1024**3 and r['peak_rss_bytes']<8*1024**3
 for n,h in r['source_hashes'].items():
  p=L/n
  if p.exists() and sha(p)==h:accepted[p.stem]={'attempt':a,'receipt':str((E/a/'receipt.json').relative_to(R)),'source_sha256':h,'object_sha256':r.get('object_sha256'),'wall_seconds':r['wall_seconds'],'print_axioms':r['print_axioms']}
for p in L.glob('Port17RELEASE_*.lean'):
 s=p.read_text();assert not re.search(r'\b(sorry|admit|axiom|native_decide|bv_decide)\b|set_option\s+(maxHeartbeats|maxRecDepth)',s),p
 assert p.stem in accepted,('current source has no successful receipt',p)
 if 'theorem ' in s:assert accepted[p.stem]['print_axioms'],p
# All changes are job-owned research/tool/evidence files, including immutable byte copies.
base='aab7c6fe684835c47c5495287ced886dbd83e903'
changed=subprocess.check_output(['git','diff','--name-only',base],cwd=R,text=True).splitlines()
for p in changed:
 assert p.startswith(('tools/port17release-20261024/','evidence/port17release-20261024/','docs/research/100bit-spend-path-20261013/lean/Port17RELEASE_')),p
for p in E.rglob('*.json'):assert p.stat().st_size<=5_000_000,('derived JSON exceeds delivery policy',p)
report={'schema':'focused-extractor-proof-packet-v1','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'inherited_charged':250,'new_charged':len(configs),'soundness_charged':250+len(configs),'ceiling':276,'kani_new':0,'heavy_rust_backend_extraction_new':0,'current_compiled_targets':accepted,'current_accepted_root_targets':{k:v for k,v in accepted.items() if k not in ['Port17RELEASE_Prepare','Port17RELEASE_Effects','Port17RELEASE_Driver','Port17RELEASE_Accounting','Port17RELEASE_Audit']},'provisional_mixed_cache_targets':[k for k in accepted if k in ['Port17RELEASE_Prepare','Port17RELEASE_Effects','Port17RELEASE_Driver','Port17RELEASE_Accounting','Port17RELEASE_Audit']],'composition_status':'WITHHELD: cached source/declaration compatibility unresolved; see compatibility.json','failed_or_preflight_charges':failed,'full_frozen_manifest_replay':False,'whole_driver_1161_without_residual_premises':False,'native_or_deployed_security_target_established':False}
(E/'manifest.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'compiled_current':len(accepted),'composition_accepted':False,'charged':len(configs),'failed_or_preflight':len(failed),'standard_axioms_only':True}))
