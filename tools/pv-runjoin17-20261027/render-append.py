"""Bind checked append cells through symbolic source steps; no recurrence evaluation."""
from pathlib import Path
import re,sys,json
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';data=(L/'PV_RunJoin_OutputData16.lean').read_text()
get=lambda a,b:list(map(int,re.search(rf'def s_{a}_{b} .*? := !\[(.*?)\]',data)[1].split(',')))
arr=lambda xs:'Array.make 8#usize ['+','.join(str(x)+'#u32' for x in xs)+']'
vec=lambda xs:'!['+','.join(map(str,xs))+']'
s='''import R1Z.PV_RunJoin_OutputPair17
import R1Z.PV_Src_Forest_AppendArguments
import R1Z.PV_Src_RootFieldMeaning
'''+''.join(f'import R1Z.PV_RunJoin_OutputCell{a:02}17\n' for a in range(41,81))+'''set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_AppendNative17
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_RunJoin_ReferenceFixtureResults PV_RunJoin_OutputPair17
local notation "M" => PV_RunJoin_FixtureRecords.M
attribute [local irreducible] R0P.nodeCompress R0P.poseidonPermutation

theorem step (w : RW) (p : RP) (n next : Usize) (c sib target : Array U32 8#usize)
    (hz : next ≠ 0#usize) (hs : Usize.wrapping_sub next 1#usize = n)
    (hc : app_cur_r w p n = ok c) (hb : app_bit_r p n = ok false)
    (hsib : app_sib_r p n = ok sib) (hn : node_digest_r c sib = ok target) :
    app_cur_r w p next = ok target := by
  rw [app_cur_r,if_neg hz]
  simp only [lift,bind_tc_ok]
  rw [hs,hc]
  simp only [bind_tc_ok]
  rw [hsib,hb]
  simp only [bind_tc_ok,ordered_r,Bool.false_eq_true,if_false]
  exact hn
#print axioms step
'''
for label,start in [('transfer',41),('withdrawal',61)]:
 for j in range(21):
  if j==0:s+=f'abbrev {label}0 := {label}Pair\n'
  else:s+=f'def {label}{j} : Array U32 8#usize := {arr(get(start+j-1,23)[:8])}\n'
 s+=f'''theorem {label}_zero : app_cur_r {label}Witness {label}Public 0#usize = ok {label}0 := by
  rw [app_cur_r]
  exact {label}_raw
#print axioms {label}_zero
'''
 for j in range(20):
  a=start+j;xs=get(a,0);left=vec(xs[:8]);right=vec(xs[8:15]+[(xs[15]-0x41531005)%2147483647]);out=vec(get(a,23)[:8])
  s+=f'''theorem {label}_node{j} : node_digest_r {label}{j} PV_Src_CanonicalRoots.table.val[{j}]! = ok {label}{j+1} := by
  apply PV_RunJoin_NodeValue17.source
  · exact PV_Src_CanonicalRoots.canonical ⟨{j},by decide⟩
  · intro k hk; interval_cases k <;> decide
  · have hl : digK (K := M) {label}{j} = {left} := by
      funext i; fin_cases i <;> rfl
    have hr : digK (K := M) PV_Src_CanonicalRoots.table.val[{j}]! = {right} := by
      have he : digK (K := M) PV_Src_CanonicalRoots.table.val[{j}]! = PV_RunJoin_RootModel.literal ⟨{j},by decide⟩ := by
        with_unfolding_all exact ((PV_Src_RootFieldMeaning.source ⟨{j},by decide⟩).trans (PV_RunJoin_RootModel.frozen_literal ⟨{j},by decide⟩))
      apply he.trans
      funext i; fin_cases i <;> rfl
    have ht : digK (K := M) {label}{j+1} = {out} := by
      funext i; fin_cases i <;> rfl
    rw [hl,hr,ht]
    exact PV_RunJoin_OutputModel16.node_{a}
#print axioms {label}_node{j}

theorem {label}_prefix{j+1} : app_cur_r {label}Witness {label}Public {j+1}#usize = ok {label}{j+1} := by
  apply step _ _ {j}#usize _ {label}{j} PV_Src_CanonicalRoots.table.val[{j}]!
  · decide
  · apply UScalar.eq_of_val_eq
    rw [usub _ _ (by simp)]
    rfl
  · exact {label+'_zero' if j==0 else label+'_prefix'+str(j)}
  · rw [PV_Src_Forest_AppendArguments.append_bit _ _ (by decide)]
    rfl
  · rw [PV_Src_Forest_AppendArguments.append_sibling _ _ (by decide)]
    rfl
  · exact {label}_node{j}
#print axioms {label}_prefix{j+1}
'''
 s+=f'''theorem {label} : CopyRecords.append_root ⟨{label}Witness,{label}Public⟩ = ok {label}20 := by
  rw [CopyRecords.append_root,{label}_prefix20]
  with_unfolding_all rfl
#print axioms {label}
'''
s+='end R1Z.PV_RunJoin_AppendNative17\n';p=L/'PV_RunJoin_AppendNative17.lean'
if '--check' in sys.argv:assert p.read_text()==s
else:p.write_text(s)
print('append source candidate checked: 40 named node consumers, no root/hash recurrence evaluation')
