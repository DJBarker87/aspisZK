import NDO_JGo_TX2_NewWeights
import RPz7_FIp_Equality
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGo_TX2_PairGuard
open Aeneas Aeneas.Std Result

theorem same2 : JGo_TX2_WeightData.f02=JGo_TX2_WeightData.f22 := by rfl
#print axioms same2
theorem same3 : JGo_TX2_WeightData.f03=JGo_TX2_WeightData.f23 := by rfl
#print axioms same3

/-- Source comparison reflexivity; list induction avoids evaluation of a
concrete comparison tree. Same proof shape as the uncached S2K_Equality lemma. -/
theorem array_self {n : Usize} (a : Array FIo_Install.NQ n) :
    core.array.equality.PartialEqArray.eq FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 a a=ok true := by
  have ne (q : FIo_Install.NQ) :
      FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne q q=ok false := by
    simp [FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31,
      core.cmp.PartialEq.ne.default,core.cmp.PartialEq.ne.trait_default,FIp_Equality.qm]
  have self : ∀ xs : List FIo_Install.NQ,
      List.allM (fun (x,y)=>do
        let b ← FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne x y
        ok (¬ b)) (List.zip xs xs)=ok true := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simpa [List.zip_cons_cons,List.allM,ne,FIp_Equality.qm] using ih
  unfold core.array.equality.PartialEqArray.eq
  rw [if_pos rfl]
  exact self a.val
#print axioms array_self

def row (r : Array FIn_WeightsExtract.field.QM31 4#usize) :=
  FIn_WeightsInstall.mapArray FIo_Install.toQ r

/-- Only the actual fixed-input branch selection, not Pair success. -/
theorem source : FIo_Native.weights.shared_two_point_guard
    (FIo_Install.toWeights JGo_TX2_WeightData.value) 2#usize=ok true := by
  have variant : FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq
      .S2 .S2=ok true := by simp [FIo_Native.transport.Variant.Insts.CoreCmpPartialEqVariant.eq]
  unfold FIo_Native.weights.shared_two_point_guard
  have variantPin : (FIo_Install.toWeights JGo_TX2_WeightData.value).variant=.S2 := by rfl
  rw [variantPin,variant,bind_tc_ok,if_pos rfl,if_pos rfl]
  change (do
    let b ← core.array.equality.PartialEqArray.eq
      FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
      (row JGo_TX2_WeightData.f02) (row JGo_TX2_WeightData.f22)
    if b then
      core.array.equality.PartialEqArray.eq
        FIo_Native.aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31
        (row JGo_TX2_WeightData.f03) (row JGo_TX2_WeightData.f23)
    else ok false)=ok true
  rw [←same2,←same3,array_self,bind_tc_ok,if_pos rfl]
  exact array_self _
#print axioms source
end AspisR1.JGo_TX2_PairGuard
end
