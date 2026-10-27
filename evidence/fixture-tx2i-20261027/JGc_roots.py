"""Named model-tree roots over the checked hash windows; max one level/module."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
tree=json.loads((P/'JGc_MERKLE_PREFLIGHT.json').read_text())['trees'][2];plan=json.loads((P/'JGc_HASH_PLAN.json').read_text())
owner={i:r['module'] for r in plan for i in r['hashes']}
ls=lambda xs:'['+','.join(map(str,xs))+']'
files={};prev={row['index']:i for i,row in enumerate(tree['hashes'][:12])};levels=[]
head='set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.JGc_TX2_M2Roots\nopen AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep\nopen OracleDecisionMultiTree\n'
end='end AspisR1.JGc_TX2_M2Roots\nend\n'
def cert(i):
 h=f'JGc_TX2_M2.Hash{i:03}'
 blocks=tree['hashes'][i]['blocks']-1
 s=f'def input{i:03} : Bytes := JGc_TX2_HashBytes.bytes {h}.message\ndef value{i:03} : State := JFp_SHADigest.output {h}.result\n'
 for j in range(blocks):
  s+=f'theorem cast{i:03}_{j} : (JGc_TX2_HashBytes.bytes {h}.B{j:02}.input).map Fin.val={h}.B{j:02}.input := by rfl\n#print axioms cast{i:03}_{j}\n'
 s+=f'theorem tail{i:03} : (JGc_TX2_HashBytes.bytes {h}.tail).map Fin.val={h}.tail := by rfl\n#print axioms tail{i:03}\n'
 s+=f'theorem numeric{i:03} : (JGc_TX2_HashBytes.bytes {h}.message).map Fin.val={h}.message := by\n'
 s+=f'  simp only [{h}.message,{h}.head,List.flatten_cons,List.flatten_nil,List.append_nil,JGc_TX2_HashBytes.append,List.map_append,'+','.join(f'cast{i:03}_{j}' for j in range(blocks))+f',tail{i:03}]\n#print axioms numeric{i:03}\n'
 s+=f'theorem hash{i:03} : JFp_SHADigest.digest input{i:03}=value{i:03} := by\n  unfold input{i:03} JFp_SHADigest.digest\n  rw [numeric{i:03},{h}.checked]\n#print axioms hash{i:03}\n'
 return s
# All messages >=64 use the symbolic head/tail emitter.
imports=''.join('import '+owner[i]+'\n' for i in range(0,12,2))
s=imports+'import JGc_TX2_ByteAppend\nimport JGc_TX2_HashBytes\nimport OracleDecisionMultiBuild\n'+head
for i in range(12):
 s+=cert(i)+f'''def tree{i:03} : Tree := .opened input{i:03}
theorem root{i:03} : root JFp_SHADigest.digest tree{i:03}=value{i:03} := hash{i:03}
#print axioms root{i:03}
'''
files[R/'lean/JGc_TX2_M2Leaves.lean']=s+end
# Sparse physical-layout coordinates, each height contains at most12 frontier bases.
coords={};frontier0={row['index']:i for i,row in enumerate(tree['hashes'][:12])}
for lev in range(18):
 after={};missing=[]
 for i,row in enumerate(tree['hashes']):
  if row['kind']!='parent' or row['level']!=lev:continue
  for side in [0,1]:
   idx=2*row['index']+side
   if idx not in frontier0:missing.append((idx*(2**lev),row['message'][1+32*side:33+32*side]))
  after[row['index']]=i
 coords[lev]=sorted(missing);frontier0=after
layout='import JGc_TX2_HashBytes\nimport OracleDecisionMultiBuild\n'+head
layout+='def indices : List Nat := '+ls(list(prev))+'\n'
layout+='def bases (height : Nat) : List Nat := match height with\n'
for lev,cs in coords.items():layout+=f'  | {lev} => '+ls([b for b,_ in cs])+'\n'
layout+='  | _ => []\n'
layout+='def siblingAt (height base : Nat) : State := match height with\n'
for lev,cs in coords.items():
 layout+=f'  | {lev} => match base with\n'
 for b,bs in cs:layout+=f'    | {b} => JGc_TX2_HashBytes.state '+ls(bs)+'\n'
 layout+='    | _ => JGc_TX2_HashBytes.state []\n'
layout+='  | _ => JGc_TX2_HashBytes.state []\n'
layout+='def SiblingLaw (f : Nat → Nat → State) : Prop := ∀ h,h<18 → ∀ b,b∈bases h → f h b=siblingAt h b\n'
layout+='''theorem unoccupied (f : Nat → Bytes) (g : Nat → Nat → State) (h b : Nat)
    (no : ¬OracleDecisionMultiBuild.Occupied indices h b) :
    OracleDecisionMultiBuild.build indices f g h b=.supplied (g h b) := by
  cases h <;> simp only [OracleDecisionMultiBuild.build,if_neg no]
#print axioms unoccupied
'''
files[R/'lean/JGc_TX2_M2Layout.lean']=layout+end
# Add the leaf input lookup and generic leaf shape certificates.
f=R/'lean/JGc_TX2_M2Leaves.lean';s=files[f].replace('import OracleDecisionMultiBuild','import JGc_TX2_M2Layout');s=s[:-len(end)]
s+='def inputAt (base : Nat) : Bytes := match base with\n'
for idx,i in prev.items():s+=f'  | {idx} => input{i:03}\n'
s+='  | _ => []\n'
s+='def InputLaw (f : Nat → Bytes) : Prop := ∀ b,b∈indices → f b=inputAt b\n'
for idx,i in prev.items():
 s+=f'''theorem shape{i:03} (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (_siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g 0 {idx}=tree{i:03} := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices 0 {idx}),inputs {idx} (by decide)]
  rfl
#print axioms shape{i:03}
'''
files[f]=s+end
last='JGc_TX2_M2Leaves'
for level in range(18):
 inds=[i for i,r in enumerate(tree['hashes']) if r['kind']=='parent' and r['level']==level]
 s=f'import {last}\n'+''.join('import '+m+'\n' for m in sorted({owner[i] for i in inds}))+head
 after={}
 for i in inds:
  row=tree['hashes'][i];idx=row['index'];left=prev.get(idx*2);right=prev.get(idx*2+1)
  def child(j,bs):return (f'tree{j:03}',f'value{j:03}',f'root{j:03}') if j is not None else (f'(.supplied (JGc_TX2_HashBytes.state {ls(bs)}))',f'(JGc_TX2_HashBytes.state {ls(bs)})','')
  l,lv,lp=child(left,row['message'][1:33]);r,rv,rp=child(right,row['message'][33:65])
  s+=cert(i)
  s+=f'''theorem address{i:03} : BinMerkle32Path.nodeInput (children {lv} {rv})=input{i:03} := by rfl
#print axioms address{i:03}
def tree{i:03} : Tree := .branch {l} {r}
theorem root{i:03} : root JFp_SHADigest.digest tree{i:03}=value{i:03} := by
  rw [tree{i:03},root{','+lp if lp else ''}{','+rp if rp else ''}]
  exact (congrArg JFp_SHADigest.digest address{i:03}).trans hash{i:03}
#print axioms root{i:03}
'''
  # Local shape uses only checked finite membership and source leaf/sibling laws.
  base=idx*(2**(level+1))
  s+=f'''theorem shape{i:03} (f : Nat → Bytes) (g : Nat → Nat → State) (inputs : InputLaw f) (siblings : SiblingLaw g) :
    OracleDecisionMultiBuild.build indices f g {level+1} {base}=tree{i:03} := by
  rw [OracleDecisionMultiBuild.build,if_pos (by decide : OracleDecisionMultiBuild.Occupied indices {level+1} {base})]
'''
  for side,j in [(0,left),(1,right)]:
   if j is not None:s+=f'  rw [shape{j:03} f g inputs siblings]\n'
   else:
    cb=(2*idx+side)*(2**level)
    s+=f'  rw [unoccupied f g {level} {cb} (by decide),siblings {level} (by decide) {cb} (by decide)]\n'
  s+='  rfl\n'+f'#print axioms shape{i:03}\n'
  after[idx]=i
 module=f'JGc_TX2_M2Level{level:02}';files[R/'lean'/(module+'.lean')]=s+end;last=module;prev=after
 levels.append(dict(module=module,level=level,hashes=inds))
files[P/'JGc_ROOT_PLAN.json']=json.dumps(levels,indent=2)+'\n'
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('root generator:',len(files),'files; leaf, then18 levels; model authentication only until byte/shape/native joins')
