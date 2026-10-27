from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
s=''.join(f'import R1Z.PV_RunJoin_IndexedRound{r:02}19\n' for r in range(22))+'''import R1Z.PV_Src_PortInitialConstants
import R1Z.PV_Src_PortInternalConstants
import R1Z.PV_Src_PortFinalConstants
set_option autoImplicit false
namespace R1Z.PV_RunJoin_IndexedCopy19
open Aeneas Aeneas.Std Result R0Z.WriterRefine R0Z.PoseidonRefine
open BuilderForestStdPort BuilderForestAdmissionPort PV_Src_PortSboxStep
local instance : ExternalLinear := PV_Src_ExternalReference.dictionary
'''
for r in range(22):
 tab='EXTERNAL_INITIAL' if r<4 else 'INTERNAL' if r<18 else 'EXTERNAL_FINAL';k=r if r<4 else r-4 if r<18 else r-18
 canon='PV_Src_PortInitialConstants.canonical' if r<4 else 'PV_Src_PortInternalConstants.canonical' if r<18 else 'PV_Src_PortFinalConstants.canonical'
 tbl='PV_Src_PortTables.initial' if r<4 else 'PV_Src_PortTables.internal' if r<18 else 'PV_Src_PortTables.final_constants'
 copy=f'R0PoseidonCopy.full_round s R0PoseidonCopy.{tab}.val[{k}]!' if r<4 or r>=18 else f'R0PoseidonCopy.internal_round s R0PoseidonCopy.INTERNAL.val[{k}]! R0PoseidonCopy.INTERNAL_SHIFTS'
 s+=f'''theorem copy{r:02} (s : State) (hs : Canonical s) :
    poseidon2.apply_round_by_index s {r}#usize =
      (do let out ← R0PoseidonCopy.apply_round s {r}#usize; ok (some (),out)) := by
  rw [PV_RunJoin_IndexedRound{r:02}19.source s hs ({canon} ⟨{k},by decide⟩)]
  rw [{tbl}]
  have hc : R0PoseidonCopy.apply_round s {r}#usize = {copy} := by
    rw [R0PoseidonCopy.apply_round]
'''
 if r<4:s+='    rw [if_pos (by decide)]\n'
 else:
  s+='    rw [if_neg (by decide)]\n'
  s+='    rw [if_pos (by decide)]\n' if r<18 else '    rw [if_neg (by decide)]\n'
  s+='    simp only [lift,bind_tc_ok]\n'
  if r>=18:
   s+=f'''    have hi : Usize.wrapping_sub {r}#usize 18#usize = {k}#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
'''
  else:
   s+=f'''    have hi : Usize.wrapping_sub {r}#usize 4#usize = {k}#usize := by
      apply UScalar.eq_of_val_eq
      rw [R0Z.WriterRefine.usub _ _ (by simp)]
      rfl
    rw [hi]
'''
 s+=f'''    have hk : Array.index_usize R0PoseidonCopy.{tab} {k}#usize = ok R0PoseidonCopy.{tab}.val[{k}]! := by
      with_unfolding_all rfl
    rw [hk]
    rfl
  rw [hc]
#print axioms copy{r:02}
'''
s+='''theorem source (s : State) (hs : Canonical s) (r : Fin 22) :
    poseidon2.apply_round_by_index s (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)) =
      (do let out ← R0PoseidonCopy.apply_round s (Usize.ofNatCore r.val (by have := r.isLt;scalar_tac)); ok (some (),out)) := by
  fin_cases r
'''
s+=''.join(f'  · exact copy{r:02} s hs\n' for r in range(22))
s+='#print axioms source\nend R1Z.PV_RunJoin_IndexedCopy19\n';(L/'PV_RunJoin_IndexedCopy19.lean').write_text(s)
