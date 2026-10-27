import R1Z.PV_L2_F3Law
import R1Z.CouplingR1PBin

/-! Exact posterior uniformity, derived from conditional fibres. Averaging
additive translations supplies the independent value coordinate while keeping
the original success/failure and history. No marginal-to-joint inference. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L2_F3Disintegration
open R0Z R0Z.FsAbortBounds R1Z.CouplingR1PBin R1Z.PV_L2_F3Law
attribute [local instance] Classical.propDecidable
variable {Input A H : Type} [Fintype Input] [AddCommGroup A] [Fintype A]

theorem posterior_uniform (decode : Input → Option (A × H))
    (fibres : ∀ h a b,
      (Finset.univ.filter (fun i => decode i = some (a,h))).card =
        (Finset.univ.filter (fun i => decode i = some (b,h))).card)
    (test : Option (A × H) → ℚ) :
    mean (fun i => test (decode i)) =
      mean (fun i => mean (fun a : A => test ((decode i).map (fun p => (a,p.2))))) := by
  have translated (b : A) : mean (fun i => test ((decode i).map (fun p => (p.1+b,p.2)))) =
      mean (fun i => test (decode i)) :=
    conditional_test decode fibres (fun _ => Equiv.addRight b) test
  have all : mean (fun b : A => mean (fun i =>
      test ((decode i).map (fun p => (p.1+b,p.2))))) = mean (fun i => test (decode i)) := by
    simp only [translated,mean_const']
  rw [mean_comm] at all
  rw [←all]
  congr 1
  funext i
  cases hd : decode i with
  | none => simp only [Option.map_none,mean_const']
  | some pair =>
    simp only [Option.map_some]
    exact mp_equiv (Equiv.addLeft pair.1) (fun a => test (some (a,pair.2)))

/-- A retained-history-dependent kernel with equal uniform means can replace
another kernel inside the ACTUAL decoder law. Failure's test is identical. -/
theorem conditional_kernel (decode : Input → Option (A × H))
    (fibres : ∀ h a b,
      (Finset.univ.filter (fun i => decode i = some (a,h))).card =
        (Finset.univ.filter (fun i => decode i = some (b,h))).card)
    (left right : A → H → ℚ) (failure : ℚ)
    (means : ∀ h, mean (fun a => left a h) = mean (fun a => right a h)) :
    mean (fun i => match decode i with | none => failure | some (a,h) => left a h) =
      mean (fun i => match decode i with | none => failure | some (a,h) => right a h) := by
  rw [posterior_uniform decode fibres (fun | none => failure | some (a,h) => left a h),
    posterior_uniform decode fibres (fun | none => failure | some (a,h) => right a h)]
  congr 1
  funext i
  cases hd : decode i with
  | none => rfl
  | some pair => exact means pair.2

#print axioms posterior_uniform
#print axioms conditional_kernel
end R1Z.PV_L2_F3Disintegration
