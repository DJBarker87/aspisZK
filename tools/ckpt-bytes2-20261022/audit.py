#!/usr/bin/env python3
"""Focused source/receipt/axiom/resource audit, no compilation or host writes."""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2]
E=R/'docs/research/100bit-spend-path-20261013/evidence/ckpt-bytes2-20261022'
BASE='77727a08b66a3d7d89ad5c854d9b4b254b7adab9'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
subprocess.run(['python3','-B',str(R/'tools/ckpt-bytes2-20261022/generate_body.py'),'--check'],check=True)
subprocess.run(['python3','-B',str(R/'tools/ckpt-bytes2-20261022/source_check.py')],check=True)
m=json.loads((E/'manifest.json').read_text()); finals=[a for a in m['attempts'] if a['final_current']]
expected={'CheckpointBytesBody','CheckpointBytesReaderWidth','CheckpointBytesDecodeC5','CheckpointBytesBodyDecodeJoin','CheckpointBytesRoundtripBoundary','CheckpointBytesSuccess','CheckpointBytes2Freeze'}
assert {a['module'] for a in finals}==expected
allowed={'propext','Classical.choice','Quot.sound'};theorems=0;finalrows=[]
for a in finals:
 assert a['exit']==0 and a['swaps']==0 and a['axioms_accepted']
 p=R/'docs/research/100bit-spend-path-20261013/lean'/(a['module']+'.lean')
 assert sha(p)==a['source_sha256']
 d=E/(a['module']+'-'+str(a['attempt']))
 assert (d/'source.lean.txt').read_bytes()==p.read_bytes()
 assert json.loads((d/'receipt.json').read_text())==a
 assert sha(Path(a['argv'][a['argv'].index('-o')+1]))==a['object_sha256']
 for imp in a['direct_imports']: assert sha(Path(imp['path']))==imp['sha256']
 text=p.read_text()
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|bv_decide|maxRecDepth|maxHeartbeats)\b',re.sub(r'/--?[\s\S]*?-/', '',text))
 names=re.findall(r'^theorem\s+(\w+)',text,re.M)
 assert all(re.search(r'^#print axioms '+re.escape(n)+r'\b',text,re.M) for n in names)
 if a['module']!='CheckpointBytes2Freeze':theorems+=len(names)
 assert len(a['axioms'])>=len(names)
 for report in a['axioms']:
  if 'depends on axioms:' in report:
   assert {s.strip() for s in report.split('[',1)[1].rsplit(']',1)[0].split(',')}<=allowed
 finalrows.append({k:a[k] for k in ['module','attempt','source_revision','exit','wall_seconds','peak_rss_bytes','swaps','axioms']})
kani=[]
for name in ['k-section-current-1','k-roundtrip-current-1','e-section-1','e-roundtrip-1']:
 p=E/'kani'/name;r=json.loads((p/'receipt.json').read_text())
 assert r['exit_status']==0 and r['swaps']==0
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
 assert r['environment']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert r['environment']['CARGO_BUILD_JOBS']=='4'
 assert 'VERIFICATION SUCCESSFUL' in (p/'stdout.log').read_text()
 assert '--unwinding-assertions' in r['target'] and not any('stub' in x for x in r['target'])
 for path,h in r['source_sha256'].items():
  if (R/path).exists():assert sha(R/path)==h,(name,path)
 reservation=json.loads((E/'kani'/('reservation-'+name+'.json')).read_text())
 assert reservation['allowed'] and reservation['bounded_reserved_bytes']+8*2**30<=55*2**30
 kani.append({k:r[k] for k in ['attempt','target','source_revision','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']})
# Check the complete changed path scope, including staged/untracked work.
changed=subprocess.check_output(['git','diff','--name-only',BASE],cwd=R,text=True).splitlines()
changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
for n in set(changed):
 assert n.startswith('tools/ckpt-bytes2-20261022/') or n.startswith(str(E.relative_to(R))+'/') or n in {'docs/research/100bit-spend-path-20261013/lean/'+x+'.lean' for x in expected},n
 p=R/n
 if p.is_file():
  assert p.suffix not in {'.olean','.o','.a','.so','.tar','.gz','.elf','.bin'}
  if p.suffix in {'.json','.jsonl'}:assert p.stat().st_size<=5_000_000
for name in expected:
 assert subprocess.run(['git','cat-file','-e',BASE+':docs/research/100bit-spend-path-20261013/lean/'+name+'.lean'],cwd=R,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL).returncode!=0
result={'schema':'focused-extractor-proof-packet-v1','base_revision':BASE,'audit_revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),'new_theorems':theorems,'final_modules':len(finals),'union_axiom_reports':len(next(a for a in finals if a['module']=='CheckpointBytes2Freeze')['axioms']),'max_lean_rss_bytes':max(a['peak_rss_bytes'] for a in finals),'lean_results':finalrows,'kani_results':kani,'shipped_changes':False,'elf_rebuild_triggered':False,'full_frozen_release_replay':False,'source_stage_join_closed':False,'status':'focused checks passed; concrete source ResumeOps/Calls adoption remains open'}
(E/'audit-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['new_theorems','final_modules','union_axiom_reports','max_lean_rss_bytes','status']}))
