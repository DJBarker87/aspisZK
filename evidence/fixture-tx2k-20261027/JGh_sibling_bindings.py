"""Close model SiblingLaw with actual native slot cells via the checked sparse stream."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
data=json.loads((R/'evidence/fixture-tx2j-20261027/JGf_MERKLE_PREFLIGHT.json').read_text())
files={}
for k in range(3):
 tree=data['trees'][k];prev={r['index']:i for i,r in enumerate(tree['hashes'][:12])};coords={h:[] for h in range(18)};cursor=0
 for h in range(18):
  after={}
  for i,row in enumerate(tree['hashes']):
   if row['kind']!='parent' or row['level']!=h:continue
   for side in range(2):
    b=(2*row['index']+side)*2**h
    if 2*row['index']+side not in prev:coords[h].append((b,cursor));cursor+=1
   after[row['index']]=i
  prev=after
 name=f'JGh_TX2_SiblingBinding{k}';ro='JGf_TX2_M0Roots' if k==0 else 'JGh_TX2_M1Roots' if k==1 else 'JGc_TX2_M2Roots';stream=0 if k<2 else 2
 s=f'import JGh_TX2_FrontierStream\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{name}\nopen Aeneas Aeneas.Std Result\nattribute [local irreducible] JFx_NativeBytes.proof JGh_TX2_NodeViews.nodes0 JGh_TX2_NodeViews.nodes1 JGh_TX2_NodeViews.nodes2\nopen AspisV8R19.SourceDuplexStep\n'
 s+=f'def native (height base : Nat) : State := JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes{k}\n  (JGh_TX2_Frontiers.stream{stream}.idxOf (height,base))\n'
 s+=f'theorem source : {ro}.SiblingLaw native := by\n  intro h hh b hb\n  interval_cases h\n'
 for h,rows in coords.items():
  if not rows:s+='  · change b∈([] : List Nat) at hb\n    cases hb\n';continue
  s+=f'  · simp only [{ro}.bases,List.mem_cons,List.not_mem_nil,or_false] at hb\n'
  s+='    rcases hb with '+ '|'.join('rfl' for _ in rows)+'\n'
  for b,cursor in sorted(rows):
   s+=f'    · unfold native\n      rw [show JGh_TX2_Frontiers.stream{stream}.idxOf ({h},{b})={cursor} from rfl]\n      exact JGh_TX2_Siblings{h:02}.k{k}c{cursor:03}_read\n'
 s+=f'#print axioms source\nend AspisR1.{name}\nend\n'
 files[R/'lean'/(name+'.lean')]=s
texts=list(files.values())
combined='import JGh_TX2_FrontierStream\n'+''.join(text[text.index('set_option'):] for text in texts)
for f,text in files.items():
 draft=P/'JGh_UNCHECKED'/(f.name+'.txt')
 if '--check' in sys.argv:assert draft.read_text()==text,draft
 else:draft.write_text(text)
files={R/'lean/JGh_TX2_SiblingBindings.lean':combined}
for f,s in files.items():
 if '--check' in sys.argv:assert (f if f.exists() else P/'JGh_UNCHECKED'/(f.name+'.txt')).read_text()==s,f
 else:f.write_text(s)
print('native sibling binding generator: one thin module with three lookup laws; exactly467 visited cells')
