import NIW_AlignFieldReply
import NIT_LowChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLowExecution
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

def step (ap0 ap1 : Powers) (i : Usize) (before : LowCells) : Result (LowCells×Low) := do
 let lhs := epick ap0 (perm (i.val%4))
 let rhs := epick ap1 (perm (i.val/4))
 let product←FIo_Native.aspis_core.field.wide_exact.WideExact.mul lhs rhs
 let scalar←FIo_Native.aspis_core.field.M31.mul FIo_Native.weights.QUARTER FIo_Native.weights.QUARTER
 let scaled←FIo_Native.aspis_core.field.wide_exact.WideExact.mul_m31 product scalar
 let after←Array.update before i scaled
 ok (after,⟨lhs,rhs,product,product,scaled,scalar,FIo_Native.weights.QUARTER,
  FIo_Native.weights.QUARTER,[0,1,2],3⟩)

theorem observed (ap0 ap1 : Powers) (h0 : canonical ap0) (h1 : canonical ap1)
 (i : Usize) (small : i.val<16) (before : LowCells) (hc : canonical before) :
 NIW_AlignFieldReply.Produced (step ap0 ap1 i before) (fun result=>
  cutLow ap0 ap1 i.val before result.2 result.1 ∧
  EMul result.2.a result.2.b result.2.product ∧
  NIT_LowInterpretation.Scale result.2.scale_a result.2.scaled ∧ canonical result.1) := by
 let lhs := epick ap0 (perm (i.val%4))
 let rhs := epick ap1 (perm (i.val/4))
 have actual := NIW_AlignFieldReply.em lhs rhs (epick_canonical ap0 h0 _) (epick_canonical ap1 h1 _)
 cases call : FIo_Native.aspis_core.field.wide_exact.WideExact.mul lhs rhs with
 | fail err => simp only [call,NIW_AlignFieldReply.Produced] at actual
 | div => simp only [call,NIW_AlignFieldReply.Produced] at actual
 | ok product =>
  simp only [call,NIW_AlignFieldReply.Produced] at actual
  obtain ⟨scaled,scale,cs,sv⟩ := NHX_LowScale.total product
  have update := NIT_LowInterpretation.update_model before i scaled small
  have frame : ∀ k,k<16 → epick (NIT_ArrayFrames.put before i.val scaled) k=
   if k=i.val then scaled else epick before k := by
   intro k hk
   exact NIT_ArrayFrames.pick_put NHI_Scalar.zero before i.val scaled small k
  unfold step
  dsimp only
  change FIo_Native.aspis_core.field.wide_exact.WideExact.mul
   (epick ap0 (perm (i.val%4))) (epick ap1 (perm (i.val/4)))=ok product at call
  rw [call,bind_tc_ok,NHX_LowScale.square,bind_tc_ok,scale,bind_tc_ok,update,bind_tc_ok]
  simp only [FIo_Native.weights.QUARTER]
  exact ⟨⟨small,h0,h1,hc,actual.2,cs,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,frame⟩,
   actual.1,sv,NHM_ArrayPreserve.canonical canonE before _ i scaled hc cs update⟩

#print axioms observed
end AspisR1.NIW_AlignLowExecution
