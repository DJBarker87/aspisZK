import NKG_FullSource
import NKG_InternalChoices
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_FullChoices
open Aeneas Aeneas.Std Result FIq_Native
open FJh_Base (State cell)
open NKG_InternalChoices (get get_ok)
def weights (l : State) := Array.make 3#usize
 [cell l (⟨1,by decide⟩ : Fin (16#usize).val),cell l (⟨9,by decide⟩ : Fin (16#usize).val),cell l (⟨10,by decide⟩ : Fin (16#usize).val)]
def even (l : State) := get (state_only_poseidon.interpolate_three_constant_columns (weights l)
 (FJb_InitialConstants.row 2) (FJe_FinalConstants.row 0) (FJe_FinalConstants.row 2)) (Array.repeat 16#usize field.QM31.ZERO)
def odd (l : State) := get (state_only_poseidon.interpolate_three_constant_columns (weights l)
 (FJb_InitialConstants.row 3) (FJe_FinalConstants.row 1) (FJe_FinalConstants.row 3)) (Array.repeat 16#usize field.QM31.ZERO)
def middle (s l : State) := get (state_only_poseidon.full_round s (even l)) (Array.repeat 16#usize field.QM31.ZERO)
def last (s l : State) := get (state_only_poseidon.full_round_packed (middle s l) (odd l)) (Array.repeat 4#usize field.QM31.ZERO)
theorem value (s l : State) (out : Array field.QM31 4#usize)
 (run : state_only_poseidon.interpolated_full_pair_packed s l=ok out) : last s l=out := by
 obtain ⟨q0,q1,q2,e,o,mid,r0,r1,r2,re,ro,rm,rf⟩ := FJe_FullCalls.value s l out run
 have e0 : q0=cell l (⟨1,by decide⟩ : Fin (16#usize).val) := Result.ok.inj
   (r0.symm.trans (RawPoseidonExternalRowReads.array_index_usize_ok l 1#usize (by decide)))
 have e1 : q1=cell l (⟨9,by decide⟩ : Fin (16#usize).val) := Result.ok.inj
   (r1.symm.trans (RawPoseidonExternalRowReads.array_index_usize_ok l 9#usize (by decide)))
 have e2 : q2=cell l (⟨10,by decide⟩ : Fin (16#usize).val) := Result.ok.inj
   (r2.symm.trans (RawPoseidonExternalRowReads.array_index_usize_ok l 10#usize (by decide)))
 subst q0;subst q1;subst q2
 have ve : even l=e := get_ok _ _ _ re
 have vo : odd l=o := get_ok _ _ _ ro
 have vm : middle s l=mid := by unfold middle;rw [ve];exact get_ok _ _ _ rm
 unfold last
 rw [vm,vo]
 exact get_ok _ _ _ rf
#print value
#print axioms value
end AspisR1.NKG_FullChoices
end
