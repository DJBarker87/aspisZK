"""Read-only current-source/receipt and text-generator preflight; runs no prover."""
from pathlib import Path
import hashlib,json,re,runpy,subprocess
P=Path(__file__).resolve().parent;R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
receipts=[json.loads(p.read_text()) for p in sorted(P.glob('JGk_TX2_*/receipt.json'))]
valid={}; records=[]
for x in receipts:
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 assert '-M7000' in x['command']
 assert x['env']['LEAN_PATH'].split(':')[0]=='/home/dombarker/project-offloads/d18-circle-model-repin-v5-20261019/attempt/objects'
 for name,h in x['source_hashes'].items():
  snapshot=P/x['attempt']/'sources'/name
  assert sha(snapshot)==h,(x['attempt'],name)
  if x['exit_status']==0:
   assert not any('sorryAx' in a or 'axioms: [sorry' in a for a in x['print_axioms'])
   for a in x['print_axioms']:
    if 'axioms: [' in a:
     axioms=a.split('axioms: [',1)[1].split(']',1)[0].split(', ')
     assert set(axioms)<= {'propext','Classical.choice','Quot.sound'}
   valid[name]={'sha256':h,'receipt':str((P/x['attempt']/'receipt.json').relative_to(R)),'axioms':x['print_axioms']}
 records.append({'attempt':x['attempt'],'target':x['sources'],'exit':x['exit_status'],'wall':x['wall_seconds'],'rss':x['peak_rss_kib'],'swap':x['swaps'],'source_revision':x['source_revision'],'source_hashes':x['source_hashes'],'axioms':x['print_axioms']})
for f in sorted((R/'lean').glob('JGk_*.lean')):
 assert f.name in valid and sha(f)==valid[f.name]['sha256'],f
 assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b',f.read_text()),f
 if re.search(r'^theorem ',f.read_text(),re.M):assert '#print axioms ' in f.read_text(),f
 assert not any(line.rstrip()!=line for line in f.read_text().splitlines()),f
# Capture generated text and compare it to the delivered source or labelled draft;
# never rewrite a checked source merely to perform a preflight.
generated=[];original_write=Path.write_text
for name in ['JGk_groups.py','JGk_positions.py','JGk_frontier_order.py','JGk_indices.py','JGk_scratch.py','JGk_scratch_indices.py','JGk_count_source.py','JGk_parent_calls.py']:
 emitted=[]
 def check_write(path,data,*args,**kwargs):
  candidate=path if path.exists() else P/'JGk_UNCHECKED'/(path.name+'.txt')
  assert candidate.exists() and candidate.read_text()==data,(name,str(path))
  emitted.append(dict(path=str(candidate.relative_to(R)),sha256=sha(candidate)))
  return len(data)
 Path.write_text=check_write
 try:runpy.run_path(str(P/name),run_name='__main__')
 finally:Path.write_text=original_write
 generated.append(dict(generator=name,emissions=emitted))
for t in range(3):
 s=(R/f'evidence/fixture-tx2k-20261027/JGh_UNCHECKED/JGh_TX2_Padding{t}.lean.txt').read_text()
 for n in ['ZeroWindows','Padding0','Padding1','Padding2','AnyFalse']:s=s.replace('JGh_TX2_'+n,'JGk_TX2_'+n)
 s=s.replace('open Aeneas Aeneas.Std Result','open Aeneas Aeneas.Std Result\nattribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2')
 s=s.replace(f'  rw [padding,List.length_drop,JGh_TX2_NodeViews.length{t}]\n  rfl',f'  rw [padding,List.length_drop,JGh_TX2_NodeViews.length{t}]')
 assert s==(R/f'lean/JGk_TX2_Padding{t}.lean').read_text()
changed=subprocess.check_output(['git','diff','--name-only','390ff8c829^'],cwd=R,text=True).splitlines()
changed+=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=R,text=True).splitlines()
assert all(f.startswith('lean/JGk_') or f.startswith('evidence/fixture-tx2l-20261027/') for f in changed)
assert (R/'lean/ARX_Root.lean').read_bytes()==(P/'JGk_BEFORE_ARX_Root.lean.txt').read_bytes()==(P/'JGk_AFTER_ARX_Root.lean.txt').read_bytes()
(P/'JGk_VALIDATION.json').write_text(json.dumps(valid,indent=2)+'\n')
(P/'JGk_ATTEMPTS.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in records))
(P/'JGk_GENERATOR_CHECKS.json').write_text(json.dumps(generated,indent=2)+'\n')
summary=dict(attempts=len(receipts),passed=sum(x['exit_status']==0 for x in receipts),failed=sum(x['exit_status']!=0 for x in receipts),kani_runs=0,delivered_modules=len(list((R/'lean').glob('JGk_*.lean'))),wall_seconds=sum(x['wall_seconds'] for x in receipts),max_peak_rss_kib=max(int(x['peak_rss_kib']) for x in receipts),swaps=sum(int(x['swaps']) for x in receipts),arx_sha256=sha(R/'lean/ARX_Root.lean'),scope='one capped host scope at a time; exact inherited launchers, d18 v5 before aspis-joint; no package replay',shipped_changes=False,top_delta={'T':0,'P':0,'G':0,'C':0},full_nonvacuity=False,accepted2=False)
(P/'JGk_SUMMARY.json').write_text(json.dumps(summary,indent=2)+'\n')
manifest={str(f.relative_to(P)):dict(sha256=sha(f),bytes=f.stat().st_size) for f in P.rglob('*') if f.is_file() and (f.suffix=='.log' or re.search(r'JGk_TX2_\d{3}/(receipt.json|stdout.log|time.log|sources/.*)$',str(f)))}
(P/'JGk_RECORDS_MANIFEST.json').write_text(json.dumps(manifest,indent=2)+'\n')
print(json.dumps(summary,indent=2))
