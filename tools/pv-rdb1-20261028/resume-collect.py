from pathlib import Path
import json,subprocess,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb1-20261028';D='/home/dombarker/project-offloads/codex-pv-rdb1-20261028';H='dombarker@100.108.41.90'
for name in ['v184-deployed-binding.json','v170-deployed-binding.json','v187-deployed-binding.json','v183-deployed-binding.json','v198-deployed-binding.json','v195-deployed-binding.json','v164-deployed-binding.json','v219-deployed-binding.json','v198-errors-config/configuration.json','v181-deployed-binding.json','v178-deployed-binding.json','v182-deployed-binding.json','witness-config/configuration.json','v181-native-config/configuration.json','preflight.json']:
 r=subprocess.run(['ssh',H,'cat '+D+'/'+name],capture_output=True,check=True);(E/name).parent.mkdir(parents=True,exist_ok=True);(E/name).write_bytes(r.stdout)
fsha=hashlib.sha256((E/'resolved-features.json').read_bytes()).hexdigest()
for p in E.glob('*-submission.json'):
 j=json.loads(p.read_text());n=j['id'];out=E/f'out-{n}.log';tm=E/f'time-{n}.log'
 if not out.exists() or not tm.exists():continue
 s=out.read_text();t=tm.read_text()
 def field(x):
  m=re.search(x+r':\s*(.+)',t);return m[1] if m else None
 j.update(target=j['module'],exit=int(field('Exit status')),wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\)'),peak_rss_kib=int(field(r'Maximum resident set size \(kbytes\)')),swap=int(field('Swaps')),print_axioms=re.findall(r"'[^\n]+' (?:depends on axioms: \[[^]]*\]|does not depend on any axioms)",s),deployed_configuration=dict(path='resolved-features.json',sha256=fsha),scope='shared run-joint.sh; MemoryHigh6G MemoryMax8G MemorySwapMax0 TasksMax128; Lean -M7000')
 (E/f'{n}-receipt.json').write_text(json.dumps(j,indent=2)+'\n')
for p in E.glob('*/receipt.json'):
 j=json.loads(p.read_text());j['deployed_configuration']=dict(path='../resolved-features.json',sha256=fsha,toolchain='1.94.1',client='devnet_spend',features=['r1p-check','aspis-r1-cost-probe/ct-host-prover'],profile='release opt3; debug_assertions=false; overflow_checks=false; panic=unwind')
 p.write_text(json.dumps(j,indent=2)+'\n')
