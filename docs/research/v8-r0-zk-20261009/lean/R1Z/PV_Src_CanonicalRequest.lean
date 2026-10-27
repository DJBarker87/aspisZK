import R1Z.PV_Src_CheckedVariants
import R1Z.PV_Src_OptionShape

/-! Canonical RspendPlus supplies the withdrawal amount without overwriting
public input data. Every original semantic admission condition is retained. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_CanonicalRequest
open Aeneas Aeneas.Std Result R0Z.WriterRefine R1J.SpendWitnessMap
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

theorem amount (i : BuilderCanonical.Instance (K := K))
    (hv : i.val.1.variant = .withdrawal) :
    i.val.1.withdrawalAmount = some (i.val.2.outputValue.val : F) := by
  have h : i.val.1.withdrawalAmount.map (ι : F →+* K) =
      some (i.val.2.outputValue.val : K) := by
    simpa only [AspisR1.SpendRelation.variantOutput,mapPub,hv,BuilderCanonical.liftWitness]
      using i.property.1.2.2.2.2.1
  cases ha : i.val.1.withdrawalAmount with
  | none => simp only [ha,Option.map_none] at h; cases h
  | some a =>
    rw [ha,Option.map_some] at h
    apply congrArg some
    apply (ι : F →+* K).injective
    simpa only [map_natCast] using Option.some.inj h

theorem word_value (v : Fin (2^30)) : w32 (v.val : F) = v32 v := by
  apply UScalar.eq_of_val_eq
  rw [w32_val,v32_val]
  change (v.val : ZMod 2147483647).val = v.val
  rw [ZMod.val_natCast,Nat.mod_eq_of_lt (by have := v.isLt; omega)]

def request (i : BuilderCanonical.Instance (K := K))
    (pool domain destination : PV_Src_PublicRecords.Context) : PV_Src_NativeInput.Request :=
  match i.val.1.variant with
  | .privateTransfer => .transfer (PV_Src_PublicRecords.transfer i.val.1 pool domain)
      (PV_Src_CheckedEncoding.recipient i.val.2)
  | .withdrawal => .withdrawal (PV_Src_PublicRecords.withdrawal i.val.1 pool domain destination)

theorem output_value (i : BuilderCanonical.Instance (K := K))
    (pool domain destination : PV_Src_PublicRecords.Context) :
    PV_Src_NativeInput.outputValue (request i pool domain destination) = v32 i.val.2.outputValue := by
  cases hv : i.val.1.variant with
  | privateTransfer => simp only [request,hv,PV_Src_NativeInput.outputValue,PV_Src_CheckedEncoding.recipient]
  | withdrawal =>
    simp only [request,hv,PV_Src_NativeInput.outputValue,PV_Src_PublicRecords.withdrawal]
    rw [amount i hv,Option.getD_some,word_value]

#print axioms amount
#print axioms word_value
#print axioms output_value
end R1Z.PV_Src_CanonicalRequest
