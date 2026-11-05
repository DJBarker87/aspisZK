import NIW_AlignFinalCollect
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignFinalSource
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairComposition

theorem source (parts powers : Parts) (hp : canonical parts) (hk : canonical powers) :
 let observed := NIW_AlignFinalCollect.collect parts powers 8
  ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero)
 FIo_Native.weights.Weights.pair_loop17 {start:=0#usize,«end»:=7#usize}
  parts powers NHI_Scalar.zero=observed.1 ∧
 NIW_AlignFieldReply.Produced observed.1 (fun out=>
  FinalTrace parts powers 8 ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) out ∧ canonE out) := by
 have trace := NIW_AlignFinalCollect.trace parts powers hp hk 8
  ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero) rfl (by change (0:Nat)≤7;omega)
  NHI_Scalar.zero_canonical (by change (7:Nat)-0<8;omega)
 cases result : (NIW_AlignFinalCollect.collect parts powers 8
  ({start:=0#usize,«end»:=7#usize},NHI_Scalar.zero)).1 with
 | fail err => simp only [result,NIW_AlignFieldReply.Produced] at trace
 | div => simp only [result,NIW_AlignFieldReply.Produced] at trace
 | ok out =>
  simp only [result,NIW_AlignFieldReply.Produced] at trace
  simp only [result,NIW_AlignFieldReply.Produced]
  exact ⟨final_loop parts powers out trace.1,trace⟩

#print axioms source
end AspisR1.NIW_AlignFinalSource
