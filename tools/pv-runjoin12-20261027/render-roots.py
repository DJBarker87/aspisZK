"""Render bounded, named mathematical root cells; no source adoption by data."""
from pathlib import Path
import json,ast,sys,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-runjoin12-20261027';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
lines=(E/'root-states.txt').read_text().splitlines();states={}
for line in lines:
 try:a,b,rest=line.split(' ',2);a=int(a);b=int(b);xs=json.loads(rest)
 except (ValueError,json.JSONDecodeError):continue
 assert len(xs)==16 and all(type(v)==int and 0<=v<2147483647 for v in xs)
 assert (a,b) not in states;states[a,b]=xs
assert set(states)=={(a,b) for a in range(21) for b in range(24)}
roots=ast.literal_eval((R/'crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal_constants.rs').read_text().split(' = ',1)[1].strip().removesuffix(';'))
vec=lambda xs:'!['+','.join(map(str,xs))+']'
def idx(j,n):return '0' if j==0 else '('+'Fin.succ ('*j+f'(0 : Fin {n-j})'+')'*j+')'
header='set_option autoImplicit false\nnoncomputable section\nnamespace R1Z.PV_RunJoin_RootModel\nopen R0P\n'
def cell(a,b):
 out=f'def s_{a}_{b} : Fin 16 → Scalar := {vec(states[a,b])}\n'
 if b==0:return out
 if b==1:expr=f'poseidonExternalLinear s_{a}_0'
 elif b<=5:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalInitial {idx(b-2,4)})'
 elif b<=19:expr=f'poseidonInternalRound s_{a}_{b-1} (poseidonInternalConstants {idx(b-6,14)})'
 else:expr=f'poseidonFullRound s_{a}_{b-1} (poseidonExternalFinal {idx(b-20,4)})'
 return out+f'theorem round_{a}_{b} : {expr} = s_{a}_{b} := by\n  funext i\n  fin_cases i <;> rfl\n#print axioms round_{a}_{b}\n'
files={'PV_RunJoin_RootModelPreflight.lean':'import R1Z.PV_RunJoin_FixtureRecords\n'+header+'abbrev Scalar := PV_RunJoin_FixtureRecords.M\n'+''.join(cell(0,b) for b in range(3))+'end R1Z.PV_RunJoin_RootModel\n'}
for a in range(21):
 assert states[a,23][:8]==roots[a]
 prev=[0]*8 if a==0 else roots[a-1]
 assert states[a,0]==prev+prev[:7]+[(prev[7]+0x41531005)%2147483647]
 text='import R1Z.PV_RunJoin_RootModelPreflight\n'+header
 text+=''.join(cell(a,b) for b in range(3 if a==0 else 0,24))
 text+=f'theorem permutation_{a} : poseidonPermutation s_{a}_0 = s_{a}_23 := by\n'
 text+='  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]\n'
 text+='  rw ['+','.join(f'round_{a}_{b}' for b in range(1,24))+']\n'
 text+=f'#print axioms permutation_{a}\n'
 text+=f'theorem parent_{a} : nodeCompress ({vec(prev)} : Fin 8 → Scalar) {vec(prev)} = {vec(roots[a])} := by\n'
 text+=f'  have hi : (fun l : Fin 16 => if h : l.val < 8 then ({vec(prev)} : Fin 8 → Scalar) ⟨l.val,h⟩ else if l.val = 15 then ({vec(prev)} : Fin 8 → Scalar) 7 - (1051521018 : Scalar) else ({vec(prev)} : Fin 8 → Scalar) ⟨l.val-8,by omega⟩) = s_{a}_0 := by\n    funext i\n    fin_cases i <;> rfl\n'
 text+=f'  unfold nodeCompress\n  rw [hi,permutation_{a}]\n  funext i\n  fin_cases i <;> rfl\n#print axioms parent_{a}\nend R1Z.PV_RunJoin_RootModel\n'
 files[f'PV_RunJoin_RootModelCell{a:02d}.lean']=text
text=''.join(f'import R1Z.PV_RunJoin_RootModelCell{a:02d}\n' for a in range(21))+header
text+='def literal : Fin 21 → Fin 8 → Scalar := !['+','.join(vec(row) for row in roots)+']\n'
text+='theorem frozen_literal (l : Fin 21) : AspisR1.AppendNode.frozenEmpty (K := Scalar) l = literal l := by\n  unfold AspisR1.AppendNode.frozenEmpty R0P.emptyRootsNat literal\n  fin_cases l <;> funext i <;> fin_cases i <;> rfl\n#print axioms frozen_literal\n'
text+='theorem initial : nodeCompress (fun _ => (0 : Scalar)) (fun _ => 0) = AspisR1.AppendNode.frozenEmpty 0 := by\n  rw [frozen_literal]\n  have hz : (fun _ : Fin 8 => (0 : Scalar)) = (![0,0,0,0,0,0,0,0] : Fin 8 → Scalar) := by\n    funext i\n    fin_cases i <;> rfl\n  rw [hz]\n  exact parent_0\n#print axioms initial\n'
text+='theorem parents (i : Fin 20) : nodeCompress (AspisR1.AppendNode.frozenEmpty (K := Scalar) i.castSucc) (AspisR1.AppendNode.frozenEmpty i.castSucc) = AspisR1.AppendNode.frozenEmpty i.succ := by\n  rw [frozen_literal,frozen_literal]\n  fin_cases i\n'
for a in range(1,21):text+=f'  · exact parent_{a}\n'
text+='#print axioms parents\nend R1Z.PV_RunJoin_RootModel\n'
files['PV_RunJoin_RootModelTable.lean']=text
for name,text in files.items():
 if '--check' in sys.argv:assert (L/name).read_text()==text,name
 else:(L/name).write_text(text)
(E/'root-model-generation.json').write_text(json.dumps(dict(classification='mathematical root-parent cells only; no source refinement or records link',max_recurrence_depth_per_cell=1,root_cells=21,round_steps=483,files={n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()}),indent=2)+'\n')
print('root model generation/check passed')
