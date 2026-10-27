from pathlib import Path
import re,sys,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
data={};models={}
for filename,model in [('FixtureHashData','FixtureHashModel'),('PathData16','PathModel16'),('OutputData16','OutputModel16')]:
 s=(L/f'PV_RunJoin_{filename}.lean').read_text()
 for m in re.finditer(r'def s_(\d+)_(\d+) .*? := !\[(.*?)\]',s):
  j,k=map(int,m.group(1,2));words=list(map(int,m[3].split(',')));assert len(words)==16 and max(words)<2147483647;data[j,k]=words;models[j]=model
out=[]
for j in range(81):
 name=f'PV_RunJoin_ValidatorCell{j:02}19';model='PV_RunJoin_'+models[j]
 imp=f'PV_RunJoin_FixtureHashCell{j}' if j<6 else f'PV_RunJoin_PathCell{j:02}16' if j<30 else f'PV_RunJoin_OutputCell{j:02}17'
 # Output30..38 have already checked complete numeric chunks with16 names.
 if 30<=j<39:imp=f'PV_RunJoin_OutputCell{j:02}16'
 if not (L/(imp+'.lean')).exists():
  candidates=[p for p in L.glob('PV_RunJoin_*.lean') if f'theorem round_{j}_1 :' in p.read_text()]
  assert len(candidates)==1,(j,candidates);imp=candidates[0].stem
 s=f'''import R1Z.PV_RunJoin_IndexedPair19
import R1Z.{imp}
set_option autoImplicit false
namespace R1Z.{name}
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
'''
 for k in range(24):
  s+=f'def s{k} : State := Array.make 16#usize ['+','.join(f'{v}#u32' for v in data[j,k])+']\n'
  s+=f'''theorem lift{k} : liftA (K := PV_RunJoin_FixtureRecords.M) s{k} = {model}.s_{j}_{k} := by
  funext i
  fin_cases i <;> rfl
#print axioms lift{k}
theorem canon{k} : Canonical s{k} := by
  intro i
  fin_cases i <;> decide
#print axioms canon{k}
'''
 s+=f'''theorem external : poseidon2.external_linear_lazy s0 = ok s1 := by
  obtain ⟨out,ho,hc,hm⟩ := PV_Src_ExternalModel.source (K := PV_RunJoin_FixtureRecords.M) s0
  have he : out = s1 := PV_RunJoin_NullifierPermutation17.state_injective out s1 hc canon1 (by
    rw [show liftA (K := PV_RunJoin_FixtureRecords.M) out = _ from funext hm,lift0,lift1]
    exact {model}.round_{j}_1)
  rw [PV_Src_ExternalReference.call_eq,ho,he]
#print axioms external
'''
 for r in range(22):
  s+=f'''theorem step{r} : poseidon2.apply_round_by_index s{r+1} {r}#usize = ok (some (),s{r+2}) := by
  apply PV_RunJoin_IndexedTarget19.round s{r+1} s{r+2} canon{r+1} canon{r+2} ⟨{r},by decide⟩
  rw [lift{r+1},lift{r+2}]
  exact {model}.round_{j}_{r+2}
#print axioms step{r}
'''
 for n in range(11):
  prev=0 if n==0 else 2*n+1
  s+=f'''theorem pair{n} : poseidon2.evaluate_trace_round_pair s{prev} {n}#usize = ok (some (s{2*n+2},s{2*n+3})) := by
  apply PV_RunJoin_IndexedPair19.source s{prev} s{2*n+1} s{2*n+2} s{2*n+3} {n}#usize (by decide)
  · '''+('rw [if_pos rfl]; exact external' if n==0 else 'rw [if_neg (by decide)]')+f'''
  · have hi : Usize.wrapping_mul 2#usize {n}#usize = {2*n}#usize := by
      apply UScalar.eq_of_val_eq
      rw [umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step{2*n}
  · have hi : Usize.wrapping_add (Usize.wrapping_mul 2#usize {n}#usize) 1#usize = {2*n+1}#usize := by
      apply UScalar.eq_of_val_eq
      rw [uadd _ _ (by rw [umul _ _ (by simp)];simp),umul _ _ (by simp)]
      rfl
    rw [hi]
    exact step{2*n+1}
#print axioms pair{n}
'''
 s+=f'end R1Z.{name}\n';p=L/(name+'.lean') if j==0 else R/'evidence/pv-runjoin19-20261027/cell-drafts'/(name+'.lean.txt')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
 out.append(dict(cell=j,module='R1Z/'+name,numeric_source=imp,round_pairs=11,numeric_recurrence_depth=0,source_bank_equation=False))
if '--check' not in sys.argv:(R/'evidence/pv-runjoin19-20261027/validator-cell-plan.json').write_text(json.dumps(out,indent=2)+'\n')
print('81 source numeric-cell transports; symbolic target and pair applications, no recurrence evaluation')
