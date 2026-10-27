from pathlib import Path
import sys
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
for r in range(22):
 kind='Initial' if r<4 else ('Internal' if r<18 else 'Final');idx=r if r<4 else (r-4 if r<18 else r-18)
 tab='EXTERNAL_INITIAL' if r<4 else ('INTERNAL' if r<18 else 'EXTERNAL_FINAL')
 val=f'poseidon2.{tab}.val[{idx}]!';isfull=kind!='Internal'
 copy=f'R0PoseidonCopy.full_round s {val}' if isfull else f'R0PoseidonCopy.internal_round s {val} R0PoseidonCopy.INTERNAL_SHIFTS'
 n=f'PV_RunJoin_IndexedRound{r:02}19'
 s=f'''import R1Z.PV_RunJoin_IndexedSbox19
import R1Z.PV_RunJoin_IndexedFinalSbox19
import R1Z.PV_Src_PortInternalRoundCopy
set_option autoImplicit false
namespace R1Z.{n}
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary

theorem source (s : State) (hs : Canonical s)
    (hc : {'Canonical '+val if isfull else val+'.val < 2147483647'}) :
    poseidon2.apply_round_by_index s {r}#usize =
      (do let out ← {copy}
          ok (some (),out)) := by
  have hlen {{α : Type}} {{n : Usize}} (a : Array α n) : Slice.len (Array.to_slice a) = n := by
    apply UScalar.eq_of_val_eq
    simp only [Slice.len_val,Array.length_to_slice]
  rw [poseidon2.apply_round_by_index]
  simp only [hlen]
  try simp only [lift,bind_tc_ok,hlen]
'''
 if r<4:s+='  rw [if_pos (by with_unfolding_all scalar_tac)]\n'
 else:
  s+='  rw [if_neg (by with_unfolding_all scalar_tac)]\n  try simp only [lift,bind_tc_ok,hlen]\n'
  s+='  have hadd : Usize.wrapping_add 4#usize 14#usize = 18#usize := by\n    apply UScalar.eq_of_val_eq\n    rw [uadd _ _ (by simp)]\n    rfl\n  rw [hadd]\n  rw [if_pos (by with_unfolding_all decide)]\n' if r<18 else '  have hadd : Usize.wrapping_add 4#usize 14#usize = 18#usize := by\n    apply UScalar.eq_of_val_eq\n    rw [uadd _ _ (by simp)]\n    rfl\n  rw [hadd]\n  rw [if_neg (by with_unfolding_all decide)]\n  rw [if_pos (by with_unfolding_all decide)]\n'
  s+='  try simp only [lift,bind_tc_ok,hlen]\n'
 index=f'{r}#usize' if r<4 else f'(Usize.wrapping_sub {r}#usize 4#usize)' if r<18 else f'(Usize.wrapping_sub (Usize.wrapping_sub {r}#usize 4#usize) 14#usize)'
 if r>=18:
  s+=f'''  have hinner : Usize.wrapping_sub {r}#usize 4#usize = {r-4}#usize := by
    apply UScalar.eq_of_val_eq
    rw [R0Z.WriterRefine.usub _ _ (by simp)]
    rfl
  rw [hinner]
'''
  index=f'(Usize.wrapping_sub {r-4}#usize 14#usize)'
 s+=f'''  have hk : Array.index_usize poseidon2.{tab} {index} = ok {val} := by
    have hsub (a b : Usize) (h : b.val ≤ a.val) : (Usize.wrapping_sub a b).val = a.val-b.val := R0Z.WriterRefine.usub a b h
    have hidx : {index} = {idx}#usize := by
      apply UScalar.eq_of_val_eq
      try rw [hsub _ _ (by simp)]
      try rw [hsub _ _ (by simp)]
      rfl
    rw [hidx]
    with_unfolding_all rfl
  rw [hk]
  simp only [bind_tc_ok]
'''
 if isfull:
  loop='loop0' if r<4 else 'loop1';p_loop='loop0_loop0' if r<4 else 'loop2_loop0';lemma='PV_RunJoin_IndexedSbox19.initial' if r<4 else 'PV_RunJoin_IndexedFinalSbox19.final_round';full='initial' if r<4 else 'final_round'
  s+=f'''  rw [poseidon2.POSEIDON2_WIDTH]
  rw [{lemma} 16 _ (by simp) (by simp)]
  simp only [← bind_assoc_eq]
  change (do let b ← PV_Src_PortFullRoundModel.{full} s {val}
             ok (some (),b)) = _
  rw [PV_Src_PortFullRoundCopy.{full} s _ hs hc]
'''
 else:
  s+=f'''  have he := congrArg (fun body : Result State => do let b ← body; ok (some (),b))
    (PV_Src_PortInternalRoundCopy.source s {val} hs hc)
  simp only [PV_Src_PortInternalRoundCopy.run,bind_assoc_eq] at he
  exact he
'''
 s+=f'#print axioms source\nend R1Z.{n}\n'
 p=L/(n+'.lean')
 if '--check' in sys.argv:assert p.read_text()==s
 else:p.write_text(s)
print('22 fixed-control symbolic round bridges; no concrete recurrence unfolded')
