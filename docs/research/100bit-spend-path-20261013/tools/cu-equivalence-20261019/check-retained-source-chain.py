#!/usr/bin/env python3
"""Reconstruct frozen production source from ten retained exact Git deltas.

This checks source coverage/order and cancellation, not semantic equivalence.
No working-tree source or real Git index is modified.
"""
from pathlib import Path
import hashlib,json,os,resource,subprocess,sys,tempfile,time
start=time.monotonic();tool=Path(__file__).resolve().parent;area=tool.parents[1];repo=tool.parents[4];ev=area/'evidence/cu-equivalence-20261019'
def git(*args,**kw):return subprocess.check_output(['git','-C',str(repo),*args],**kw)
def rev(s):return git('rev-parse',s).decode().strip()
reference=rev('f458169f7');production=rev('39c2971dd')
keep=[(1,'3ab4faf7f'),(2,'190e1779c'),(3,'d631a90ec'),(4,'d11f9b2fc'),(5,'e58b87665'),(6,'e5a93db5c'),(7,'2aa1b879c'),(10,'225a3736d'),(12,'16a39d2a8'),(14,'39c2971dd')]
reverts=[('f40c80702','ad8c22750'),('481df1dec','8cdeaf716'),('b0005af33','a29133e25'),('029206324','16724ebd0')]
roots=['crates','programs'];source_commits=git('rev-list','--reverse',reference+'..'+production,'--',*roots).decode().splitlines()
accounted={rev(c) for _,c in keep}|{rev(c) for pair in reverts for c in pair}
assert set(source_commits)==accounted,('unaccounted source commits',set(source_commits)^accounted)
cancellations=[]
for candidate,revert in reverts:
 candidate=rev(candidate);revert=rev(revert)
 assert git('diff',candidate,revert+'^','--',*roots)==b''
 assert git('diff',candidate+'^',revert,'--',*roots)==b''
 cancellations.append({'rejected_candidate':candidate,'inverse_revert':revert,'source_subtrees_equal_before_and_after':True})
steps=[]
with tempfile.TemporaryDirectory(prefix='aspis-retained-source-chain-') as tmp:
 env=dict(os.environ,GIT_INDEX_FILE=str(Path(tmp)/'index'))
 git('read-tree',reference,env=env)
 for number,candidate in keep:
  candidate=rev(candidate);parent=rev(candidate+'^');before=git('write-tree',env=env).decode().strip()
  for root in roots:assert rev(before+':'+root)==rev(parent+':'+root),(number,root,'predecessor mismatch')
  patch=git('diff','--binary',parent,candidate,'--',*roots)
  subprocess.run(['git','-C',str(repo),'apply','--cached','--whitespace=nowarn'],input=patch,env=env,check=True)
  after=git('write-tree',env=env).decode().strip()
  for root in roots:assert rev(after+':'+root)==rev(candidate+':'+root),(number,root,'candidate mismatch')
  steps.append({'candidate_number':number,'candidate':candidate,'parent':parent,'source_patch_sha256':hashlib.sha256(patch).hexdigest(),'changed_paths':git('diff','--name-only',parent,candidate,'--',*roots).decode().splitlines(),'before_subtrees':{r:rev(before+':'+r) for r in roots},'after_subtrees':{r:rev(after+':'+r) for r in roots}})
 for root in roots:assert rev(after+':'+root)==rev(production+':'+root)
assert git('diff',production,'--',*roots)==b''
u=resource.getrusage(resource.RUSAGE_SELF)
report={'status':'EXACT_TEN_RETAINED_PATCHES_RECONSTRUCT_FROZEN_PRODUCTION_SOURCE','semantic_composition_proved_by_this_check':False,'reference':reference,'production':production,'selected_features':['pool-adapter','private-leaf-salts'],'excluded_features':['prover','cu-profiling'],'source_roots':roots,'steps':steps,'cancelled_pairs':cancellations,'all_source_commits_accounted':True,'audit':{'command':[sys.executable,*sys.argv],'revision':rev('HEAD'),'features':'source tree/delta audit only','exit':0,'wall_seconds':time.monotonic()-start,'peak_rss_bytes':u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,'process_swaps':u.ru_nswap,'print_axioms':'N/A: Git source reconstruction; semantic Lean certificates separate'}}
(ev/'RETAINED-SOURCE-CHAIN.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'status':report['status'],'retained_steps':len(steps),'cancelled_pairs':len(cancellations),'unaccounted_source_commits':0}))
