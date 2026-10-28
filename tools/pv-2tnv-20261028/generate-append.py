"""Bounded per-round append certificates; no concrete recurrence is unfolded."""
from pathlib import Path
import json,hashlib,sys,re
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-2tnv-20261028/resume';x=json.load(open(E/'append-probe.json'));assert x['root_matches'] and x['carry_matches']
vec=lambda xs:'!['+','.join(map(str,xs))+']'
idx=lambda j,n:'0' if j==0 else '('+'Fin.succ ('*j+f'(0 : Fin {n-j})'+')'*j+')'
files={}
for a in range(1,21):
 states=x['cells'][a];left=states[0][:8];right=states[0][8:15]+[(states[0][15]+1051521018)%2147483647]
 s='import PV_2TNV_PublicEncoding\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.PV_2TNV_Node'+f'{a:02}'+'\nopen R0P\nabbrev M := PV_2TNV_PublicEncoding.M\n'
 for b,v in enumerate(states):s+=f'def s{b} : Fin 16 → M := {vec(v)}\n'
 for b in range(1,24):
  if b==1:expr='poseidonExternalLinear s0'
  elif b<=5:expr=f'poseidonFullRound s{b-1} (poseidonExternalInitial {idx(b-2,4)})'
  elif b<=19:expr=f'poseidonInternalRound s{b-1} (poseidonInternalConstants {idx(b-6,14)})'
  else:expr=f'poseidonFullRound s{b-1} (poseidonExternalFinal {idx(b-20,4)})'
  s+=f'theorem r{b} : {expr} = s{b} := by\n  funext i\n  fin_cases i <;> rfl\n#print axioms r{b}\n'
 s+='theorem permutation : poseidonPermutation s0 = s23 := by\n  simp only [poseidonPermutation,List.ofFn_succ,List.ofFn_zero,List.foldl_cons,List.foldl_nil]\n  rw ['+','.join('r'+str(b) for b in range(1,24))+']\n#print axioms permutation\n'
 s+=f'def left : Fin 8 → M := {vec(left)}\ndef right : Fin 8 → M := {vec(right)}\ndef output : Fin 8 → M := {vec(states[-1][:8])}\n'
 s+='''theorem source : nodeCompress left right = output := by
  have hi : (fun l : Fin 16 => if h : l.val < 8 then left ⟨l.val,h⟩
    else if l.val = 15 then right 7 - (1051521018 : M)
    else right ⟨l.val-8,by omega⟩) = s0 := by
    funext i
    fin_cases i <;> rfl
  unfold nodeCompress
  rw [hi,permutation]
  funext i
  fin_cases i <;> rfl
#print axioms source
'''+f'end AspisR1.PV_2TNV_Node{a:02}\n'
 files[f'PV_2TNV_Node{a:02}.lean']=s
receipt=dict(input_sha256=hashlib.sha256((E/'append-probe.json').read_bytes()).hexdigest(),nodes=20,rounds=460,exceptional_shapes='one named input-state equation per node; each round is isolated; no unfolded recursive hash',next_consumer='PV_2TNV_AppendBinding',files={n:hashlib.sha256(s.encode()).hexdigest() for n,s in files.items()})
for n,s in files.items():
 p=R/'lean'/n
 if '--check' in sys.argv:assert p.read_text()==s,n
 else:p.write_text(s)
if '--check' in sys.argv:assert json.load(open(E/'append-generation.json'))==receipt
else:(E/'append-generation.json').write_text(json.dumps(receipt,indent=2)+'\n')
print('checked' if '--check' in sys.argv else 'generated',len(files),'bounded nodes')
