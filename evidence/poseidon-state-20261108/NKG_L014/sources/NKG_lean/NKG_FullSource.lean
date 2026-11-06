import NKG_ColumnLoop
import NIH_FullRounds
import RPv_FJe_FullPackedValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKG_FullSource
open Aeneas Aeneas.Std Result FIq_Native
open FIv_NativeArithmetic (NQ)
open FJb_MatrixGroupStep (State)
open FIw_ArrayValue (canonical decoded)
open FJb_TailCell (cell)
/-- Both column domains come from SAME three selected weights and six pinned
constant rows. Their Results discharge both full-round domains internally. -/
theorem result (s l : State) (hs : canonical s) (hl : canonical l) :
 ∃ out,state_only_poseidon.interpolated_full_pair_packed s l=ok out ∧ canonical out ∧
 decoded out=fun g=>R0P.poseidonPackingFormula
   ExtractedMaskQmPackBase4Arithmetic.iBasis ExtractedMaskQmPackBase4Arithmetic.uBasis
   (fun j=>R0P.poseidonInterpolatedFullPair (decoded s) (decoded l) (FJe_ExternalAdjoint.lane g j)) := by
 let q0 := cell l (⟨1,by decide⟩ : Fin (16#usize).val)
 let q1 := cell l (⟨9,by decide⟩ : Fin (16#usize).val)
 let q2 := cell l (⟨10,by decide⟩ : Fin (16#usize).val)
 have r0 : Array.index_usize l 1#usize=ok q0 := RawPoseidonExternalRowReads.array_index_usize_ok l _ (by decide)
 have r1 : Array.index_usize l 9#usize=ok q1 := RawPoseidonExternalRowReads.array_index_usize_ok l _ (by decide)
 have r2 : Array.index_usize l 10#usize=ok q2 := RawPoseidonExternalRowReads.array_index_usize_ok l _ (by decide)
 have hw := (FJe_FullWeights.value l q0 q1 q2 hl r0 r1 r2).1
 obtain ⟨even,re,ce,_⟩ := NKG_ColumnLoop.source (Array.make 3#usize [q0,q1,q2])
   (FJb_InitialConstants.row 2) (FJe_FinalConstants.row 0) (FJe_FinalConstants.row 2)
   hw (FJb_InitialConstants.bounded 2) (FJe_FinalConstants.bounded 0) (FJe_FinalConstants.bounded 2)
 obtain ⟨odd,ro,co,_⟩ := NKG_ColumnLoop.source (Array.make 3#usize [q0,q1,q2])
   (FJb_InitialConstants.row 3) (FJe_FinalConstants.row 1) (FJe_FinalConstants.row 3)
   hw (FJb_InitialConstants.bounded 3) (FJe_FinalConstants.bounded 1) (FJe_FinalConstants.bounded 3)
 obtain ⟨middle,rm,cm,_⟩ := NIH_FullRounds.qm s even hs ce
 obtain ⟨out,rf,cf,_⟩ := NIH_FullRounds.packed_qm middle odd cm co
 have run : state_only_poseidon.interpolated_full_pair_packed s l=ok out := by
   simp only [state_only_poseidon.interpolated_full_pair_packed,r0,r1,r2,bind_tc_ok,
     FJb_InitialConstants.read 2#usize (by decide),FJb_InitialConstants.read 3#usize (by decide),
     FJe_FinalConstants.read 0#usize (by decide),FJe_FinalConstants.read 1#usize (by decide),
     FJe_FinalConstants.read 2#usize (by decide),FJe_FinalConstants.read 3#usize (by decide)]
   change (do
     let ev ← state_only_poseidon.interpolate_three_constant_columns (Array.make 3#usize [q0,q1,q2])
       (FJb_InitialConstants.row 2) (FJe_FinalConstants.row 0) (FJe_FinalConstants.row 2)
     let od ← state_only_poseidon.interpolate_three_constant_columns (Array.make 3#usize [q0,q1,q2])
       (FJb_InitialConstants.row 3) (FJe_FinalConstants.row 1) (FJe_FinalConstants.row 3)
     let mid ← state_only_poseidon.full_round s ev
     state_only_poseidon.full_round_packed mid od)=ok out
   simp only [re,ro,rm,rf,bind_tc_ok]
 exact ⟨out,run,FJe_FullPackedValue.value s l out hs hl run⟩
#print result
#print axioms result
end AspisR1.NKG_FullSource
end
