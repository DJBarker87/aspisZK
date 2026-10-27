"""Bind ordered model sibling cells to the two actual installed native slot views."""
from pathlib import Path
import re,json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
data=json.loads((R/'evidence/fixture-tx2j-20261027/JGf_MERKLE_PREFLIGHT.json').read_text())
ls=lambda xs:'['+','.join(map(str,xs))+']';u8=lambda xs:'['+','.join(f'{x}#u8' for x in xs)+']'
prune=['JFx_NativeBytes.proof','JFx_NativeBytes.proofBytes']+[f'JFx_DataProof{i:02}.length' for i in range(15)]
cleanup=['List.drop_append','List.take_append','List.length_append','Nat.reduceAdd','Nat.reduceMul','Nat.reduceSub','Nat.reduceLeDiff','List.length_drop','List.drop_eq_nil_of_le','List.take_of_length_le','List.drop_zero','List.take_zero','List.nil_append','List.append_nil']
levels={h:[] for h in range(18)}
for kind in range(3):
 tree=data['trees'][kind];prev={row['index']:i for i,row in enumerate(tree['hashes'][:12])};cursor=0
 for h in range(18):
  after={}
  for i,row in enumerate(tree['hashes']):
   if row['kind']!='parent' or row['level']!=h:continue
   for side in range(2):
    index=2*row['index']+side
    if index not in prev:
     levels[h].append((kind,index*2**h,cursor,row['message'][1+32*side:33+32*side],tree['slot_start']));cursor+=1
   after[row['index']]=i
  prev=after
 assert cursor==tree['consumed']
files={}
for h,rows in levels.items():
 name=f'JGh_TX2_Siblings{h:02}'
 s='import JGh_TX2_NodeViews\nimport JGc_TX2_M2Layout\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.'+name+'\nopen Aeneas Aeneas.Std Result\nopen AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge\n'
 for kind,base,cursor,bs,start in rows:
  n=f'k{kind}c{cursor:03}';off=start+32*cursor;ro='JGf_TX2_M0Roots' if kind==0 else 'JGh_TX2_M1Roots' if kind==1 else 'JGc_TX2_M2Roots'
  s+=f'def {n} : Array U8 32#usize := Array.make 32#usize {u8(bs)}\n'
  s+=f'theorem {n}_selected : ((JGh_TX2_NodeViews.nodes{kind}.val).drop {32*cursor}).take 32={n}.val := by\n  rw [JGh_TX2_NodeViews.values{kind},JFq_Range.nested _ _ {4800 if kind==2 else 5504} {32*cursor} 32 (by decide)]\n'
  s+='  simp only ['+','.join(prune+cleanup)+']\n';more=[]
  for k in range(off//4096,(off+31)//4096+1):
   mod=f'JFx_DataProof{k:02}';text=(R/'lean'/(mod+'.lean')).read_text();more += [mod+'.bytes']+[mod+'.'+x for x in re.findall(r'theorem (c\d+_length)',text)]
  s+='  simp only ['+','.join(more+cleanup)+f']\n  rfl\n#print axioms {n}_selected\n'
  s+=f'theorem {n}_decode : decodeState {n}={ro}.siblingAt {h} {base} := by\n  funext i\n  fin_cases i <;> rfl\n#print axioms {n}_decode\n'
 for k in [0,2]:
  ro=f'JGf_TX2_Count{k}'
  s+=f'theorem count{k}_frontier : OraclePortFrozenOrder.countLevel {ro}.indices{h:02}.length {ro}.indices{h:02}=({ro}.indices{h+1:02},'+str(sum(1 for row in data['trees'][0 if k==0 else 2]['hashes'] if row['kind']=='parent' and row['level']==h and row['source']!='occupied'))+') := by\n'
  s+=f'  rw [←MultiproofConeCountGroups.source_level_eq _ _ (by decide : {ro}.indices{h:02}.Pairwise (·<·))]\n  exact {ro}.level{h:02}\n#print axioms count{k}_frontier\n'
 for kind,base,cursor,bs,start in rows:
  n=f'k{kind}c{cursor:03}';ro='JGf_TX2_M0Roots' if kind==0 else 'JGh_TX2_M1Roots' if kind==1 else 'JGc_TX2_M2Roots'
  s+=f'theorem {n}_read : JGh_TX2_NodeViews.readCell JGh_TX2_NodeViews.nodes{kind} {cursor}={ro}.siblingAt {h} {base} :=\n  (JGh_TX2_NodeViews.read_selected _ _ {n} {n}_selected).trans {n}_decode\n#print axioms {n}_read\n'
 s+=f'end AspisR1.{name}\nend\n'
 files[P/'JGh_UNCHECKED'/(name+'.lean.txt')]=s
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('sibling generator:',len(files),'height modules,',sum(len(v) for v in levels.values()),'native32-byte cells')
