"""Read-only recovery of own evidence, excluding binaries and build caches."""
from pathlib import Path
import subprocess,json,hashlib,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb1-20261028';D='/home/dombarker/project-offloads/codex-pv-rdb1-20261028';H='dombarker@100.108.41.90'
paths=['project-all-source-match.json','preflight.json','v186-structural.json','source-audit.json','project-source-match.json','resolved-features.json','unit-graph.json','unit-graph.stderr','upload-admission.json','upload-admission.log']
paths+=['classify-structural/results.json']
for suite in ['std-extra','drop','join','append','reserve','pop','pop-zst','array']:paths+=['native-'+suite+'/configuration.json']
for suite in ['leaves','bytes','wide']:paths+=['classify-project-'+suite+'/'+f for f in ['inputs.json','metadata.json','Cargo.toml.txt','fixture.rs.txt']]
for p in paths:
 q=subprocess.run(['ssh',H,'cat '+D+'/'+p],capture_output=True);assert q.returncode==0,(p,q.stderr)
 dest=E/p;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(q.stdout)
features=E/'resolved-features.json';fsha=hashlib.sha256(features.read_bytes()).hexdigest()
for p in E.glob('*/receipt.json'):
 j=json.loads(p.read_text());j['deployed_configuration']=dict(toolchain='rustc 1.94.1',client='devnet_spend',features=['r1p-check','aspis-r1-cost-probe/ct-host-prover'],profile='release',debug_assertions=False,overflow_checks=False,resolved_every_crate=dict(path='../resolved-features.json',sha256=fsha),unit_graph_reproduced='deployed-unit-graph/receipt.json')
 name=p.parent.name
 if name.startswith('native-'):j['actual_fixture_configuration']='configuration.json'
 if name.startswith('project-') and name in ['project-leaves','project-bytes','project-wide']:j['actual_fixture_configuration']='../classify-project-'+name[8:]+'/inputs.json'
 j['command_sha256']=hashlib.sha256(json.dumps(j['target'],separators=(',',':')).encode()).hexdigest()
 p.write_text(json.dumps(j,indent=2)+'\n')
for n in [54700,54701,54797,54798,54799]:
 p=E/f'time-{n}.log'
 if not p.exists():continue
 t=p.read_text();out=(E/f'out-{n}.log').read_text();meta=json.loads((E/f'{n}-submission.json').read_text())
 def field(name):
  m=re.search(name+r':\s*(.+)',t);return m[1] if m else None
 receipt=dict(**meta,target=meta['module'],exit=int(field('Exit status')),wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=int(field(r'Maximum resident set size \(kbytes\)')),swap=int(field('Swaps')),print_axioms=[l for l in out.splitlines() if 'axioms' in l],deployed_configuration=dict(path='resolved-features.json',sha256=fsha),scope='shared run-joint.sh; MemoryHigh6G MemoryMax8G MemorySwapMax0 TasksMax128; Lean -M7000')
 (E/f'{n}-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('recovered',len(paths),'own artifacts; receipts enriched with exact deployed configuration')
