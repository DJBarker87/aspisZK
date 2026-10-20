from pathlib import Path
import hashlib,json,re,subprocess,sys
base=Path(__file__).resolve().parents[2]; ev=Path(__file__).resolve().parent
root=base.parents[2]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((ev/'manifest.json').read_text())
assert m['schema']=='focused-extractor-proof-packet-v1'
# Include diagnostic errors reported with Lean's newer error(code) spelling.
for r in m['attempts']:
 run=ev/r.get('evidence_dir',r['module']+'/'+r['source_sha256'][:12])
 log=(run/'lean.log').read_text()
 r['errors']=[l for l in log.splitlines() if ': error' in l]
 (run/'receipt.json').write_text(json.dumps(r,indent=2)+'\n')
(ev/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
final={}
for r in m['attempts']:
 if r['module']!='R13CloseAPICheck': final[r['module']]=r
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
# Check exact retained-source subtrees without modifying them.
subprocess.run([sys.executable,str(ev/'extract.py'),'--check'],check=True)
base_rev='eb9b122b6'
changed=subprocess.check_output(['git','diff','--name-only',base_rev],text=True).splitlines()
added=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines()
for f in changed+added:
 assert f.startswith(('docs/research/100bit-spend-path-20261013/evidence/r13-close-20261020/',
  'docs/research/100bit-spend-path-20261013/lean/R13Close','docs/research/100bit-spend-path-20261013/design/R13-CLOSE-20261020.md')),f
for f in changed:
 # Existing modules and all existing source files remain byte-identical.
 existed=subprocess.run(['git','cat-file','-e',base_rev+':'+f],capture_output=True).returncode==0
 assert not existed,f
freeze=json.loads((base/'evidence/freeze-20261020/source-hashes.json').read_text())
pins=[]
for f,digest in freeze['files'].items():
 if f.startswith(('crates/aspis-r1-cost-probe/src/','crates/aspis-core/src/')):
  p=root/f
  assert sha(p)==digest,f
  pins.append(dict(path=f,sha256=digest,bytes=p.stat().st_size))
source=base/'evidence/stage2-continuation-20261020/generated/AspisR1Stage2/Funs.lean'
assert source.read_bytes()==subprocess.check_output(['git','show',base_rev+':'+str(source.relative_to(root))])
report=dict(schema=m['schema'],status='partial-R13-open',final_modules=len(final),
 final_theorem_audits=sum(len(r['axioms']) for r in final.values()),
 historical_failed_compiles=sum(r['exit_status']!=0 for r in m['attempts']),
 final_wall_seconds=sum(r['wall_seconds'] for r in final.values()),
 final_peak_rss_bytes=max(r['peak_rss_bytes'] for r in final.values()),
 final_process_swaps=sum(r['process_swap_count'] for r in final.values()),
 final_sources=[dict(module=n,source_sha256=r['source_sha256']) for n,r in final.items()],
 frozen_verifier_files_checked=len(pins),frozen_source_revision=freeze['source_revision'],source_pins=pins,
 unchanged_existing_lean_modules=True,unchanged_retained_extraction=True,
 complete_source_model_refinement=False,tx2_caller_composition=False,
 remaining=['batch key encode/decode and whole dedup scan','parent/sibling geometry across 18 levels',
 'Iterator.any.default backend and word-decode zero law','source slot/count transport',
 'whole-run digest/log and D77 read-set transport','accepted tx2 to all 12 query paths','S7 batch A'])
(ev/'audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['source_pins','final_sources']},indent=2))
