import NIW_AlignFieldReply
import NIT_LibraChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignLibraExecution
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_FieldInterpretation NIT_PairComposition

def afterRead (f : Ref (Slice U8)) (libra : Powers) (j : Usize) (before : Parts)
 (read : Result E) : Result (Parts×LibraLog) := do
 let coefficient←read
 let weight := epick libra j.val
 let old := epick before 4
 let product←FIo_Native.aspis_core.field.wide_exact.WideExact.mul coefficient weight
 let reply←FIo_Native.aspis_core.field.wide_exact.WideExact.add old product
 let after←Array.update before 4#usize reply
 ok (after,⟨f.address,2048,j.val,coefficient,coefficient,weight,product,old,product,reply,3,[0,1,2]⟩)

def step (f : Ref (Slice U8)) (libra : Powers) (j : Usize) (before : Parts) : Result (Parts×LibraLog) :=
 afterRead f libra j before (FIo_Native.weights.field f.value j)

/-- Internal returning field case; the complete caller theorem must split the
actual read and retain its fail/div prefix. The coefficient is the observed
source reply, not a selected model coefficient. -/
theorem observed (f : Ref (Slice U8)) (size : f.value.val.length=2048)
 (libra : Powers) (cl : canonical libra) (j : Usize) (small : j.val<4)
 (before : Parts) (cb : canonical before) (coefficient : E)
 (field : FIo_Native.weights.field f.value j=ok coefficient) :
 NIW_AlignFieldReply.Produced (step f libra j before) (fun result=>
  cutLibraLog f libra j.val before result.2 result.1 ∧ result.2.coefficient=coefficient ∧
  EMul result.2.mul_a result.2.mul_b result.2.product ∧
  EAdd result.2.add_a result.2.add_b result.2.reply ∧ canonical result.1) := by
 have cc := NHE_FieldCanonical.success f.value j (by omega) coefficient field
 let weight := epick libra j.val
 let old := epick before 4
 have actual := NIW_AlignFieldReply.em coefficient weight cc (epick_canonical libra cl _)
 cases call : FIo_Native.aspis_core.field.wide_exact.WideExact.mul coefficient weight with
 | fail err => simp only [call,NIW_AlignFieldReply.Produced] at actual
 | div => simp only [call,NIW_AlignFieldReply.Produced] at actual
 | ok product =>
  simp only [call,NIW_AlignFieldReply.Produced] at actual
  have addition := NIW_AlignFieldReply.ea old product (epick_canonical before cb _) actual.2
  cases added : FIo_Native.aspis_core.field.wide_exact.WideExact.add old product with
  | fail err => simp only [added,NIW_AlignFieldReply.Produced] at addition
  | div => simp only [added,NIW_AlignFieldReply.Produced] at addition
  | ok reply =>
   simp only [added,NIW_AlignFieldReply.Produced] at addition
   have update := NIT_LowInterpretation.update_model before 4#usize reply (by decide)
   have frame : ∀ k,k<7 → epick (NIT_ArrayFrames.put before 4 reply) k=
    if k=4 then reply else epick before k := by
    intro k hk
    exact NIT_ArrayFrames.pick_put NHI_Scalar.zero before 4 reply (by decide) k
   unfold step afterRead
   rw [field,bind_tc_ok]
   dsimp only
   change FIo_Native.aspis_core.field.wide_exact.WideExact.mul coefficient (epick libra j.val)=ok product at call
   change FIo_Native.aspis_core.field.wide_exact.WideExact.add (epick before 4) product=ok reply at added
   rw [call,bind_tc_ok,added,bind_tc_ok,update,bind_tc_ok]
   exact ⟨⟨small,size,cl,cb,cc,actual.2,addition.2,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,frame⟩,
    rfl,actual.1,addition.1,NHM_ArrayPreserve.canonical canonE before _ 4#usize reply cb addition.2 update⟩

theorem failed (f : Ref (Slice U8)) (libra : Powers) (j : Usize) (before : Parts) (err : Error)
 (field : FIo_Native.weights.field f.value j=fail err) : step f libra j before=fail err := by
 unfold step afterRead
 rw [field];rfl

theorem diverged (f : Ref (Slice U8)) (libra : Powers) (j : Usize) (before : Parts)
 (field : FIo_Native.weights.field f.value j=div) : step f libra j before=div := by
 unfold step afterRead
 rw [field];rfl

#print axioms observed
#print axioms failed
#print axioms diverged
end AspisR1.NIW_AlignLibraExecution
