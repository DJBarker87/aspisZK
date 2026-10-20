from pathlib import Path
import hashlib,json,re,subprocess
base=Path(__file__).resolve().parents[2]; ev=Path(__file__).resolve().parent
root=base.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((ev/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
final={}
for r in m['attempts']: final[r['module']]=r
allowed={'propext','Classical.choice','Quot.sound'}
for name,r in final.items():
 p=base/'lean'/f'{name}.lean'
 assert r['exit_status']==0 and not r['errors'],name
 assert r['source_sha256']==sha(p),name
 assert r['process_swap_count']==0,name
 assert len(r['axioms'])==len(re.findall(r'^theorem |^private theorem ',p.read_text(),re.M)),name
 for line in r['axioms']:
  if 'does not depend on any axioms' not in line:
   names=set(re.search(r'\[([^\]]*)\]',line)[1].split(', '))
   assert names<=allowed,(name,line)
 for imp in r['direct_imports']:
  assert sha(Path(imp['object_path']))==imp['object_sha256'],(name,imp)
 assert not re.search(r'\b(sorry|admit|axiom|native_decide)\b|set_option (maxRecDepth|maxHeartbeats)',p.read_text()),name
 assert all(x in r['command'] for x in ['-j1','-M4400','-DElab.async=false']),name
# Only new research files are permitted. This comparison also covers untracked additions.
changed=subprocess.check_output(['git','diff','--name-only','712ae02b6'],text=True).splitlines()
added=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines()
for f in changed+added:
 assert f.startswith('docs/research/100bit-spend-path-20261013/'),f
for f in changed:
 assert f.startswith(('docs/research/100bit-spend-path-20261013/evidence/r13-refine-20261020/',
  'docs/research/100bit-spend-path-20261013/lean/R13','docs/research/100bit-spend-path-20261013/design/R13-REFINE-20261020.md')),f
source_paths=['crates/aspis-r1-cost-probe/src/multiproof.rs','crates/aspis-r1-cost-probe/src/candidate.rs',
 'crates/aspis-r1-cost-probe/src/verifier.rs','crates/aspis-r1-cost-probe/src/compact.rs',
 'crates/aspis-core/src/state_only_private_merkle.rs',
 'docs/research/100bit-spend-path-20261013/evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean']
pins=[]
for f in source_paths:
 p=root/f
 current=p.read_bytes(); original=subprocess.check_output(['git','show','712ae02b6:'+f])
 assert current==original,f
 pins.append(dict(path=f,sha256=sha(p),bytes=len(current),unchanged_from='712ae02b695ed6a8354349ba2b74b8846db1b1bf'))
report=dict(schema=m['schema'],status='partial-R13-open',final_modules=len(final),
 final_theorem_audits=sum(len(r['axioms']) for r in final.values()),
 failed_historical_attempts=sum(r['exit_status']!=0 for r in m['attempts']),
 final_wall_seconds=sum(r['wall_seconds'] for r in final.values()),
 final_peak_rss_bytes=max(r['peak_rss_bytes'] for r in final.values()),
 process_swap_count=sum(r['process_swap_count'] for r in final.values()),
 final_sources=[dict(module=n,source_sha256=r['source_sha256']) for n,r in final.items()],
 source_pins=pins,whole_source_to_model_acceptance_proved=False,
 remaining=['sorted-key and array-level simulation','source padding scan','whole-loop/caller reachability','R10 global log','S7/stage-1 re-pin'])
(ev/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['source_pins','final_sources']},indent=2))
