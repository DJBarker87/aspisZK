import PV_L2C_ReferenceArithmetic
import PV_L2C_NativeFold
import R1Z.ProverCommitFoldSteps
set_option autoImplicit false
namespace PV_L2C_ExtractedM31Fold
open Aeneas Aeneas.Std Result AspisR1ProverBalance9
open PV_L2C_M31 PV_L2C_ReferenceArithmetic R1Z.ProverCommitFoldSteps

def run (xs : List U32) (s : U32) : Result U32 :=
  foldSteps (fun x sum => aspis_core.field.M31.add sum x) xs s

theorem source (xs : List word) (s : word) :
    run (xs.map wrap) (wrap s)=ok (wrap (PV_L2C_NativeFold.fold xs s)) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [run,List.map_cons,foldSteps,m31_add,wrap,bind_tc_ok]
    exact ih (add s x)
#print axioms source

theorem zero_sum (xs : List word) (hc : ∀ x∈xs,canonical x)
    (hz : (xs.map decode).sum=0) :
    run (xs.map wrap) aspis_core.field.M31.ZERO=ok aspis_core.field.M31.ZERO := by
  have h0 : canonical (0 : word) := by unfold canonical p; decide
  have hc' := PV_L2C_NativeFold.fold_canonical xs hc 0 h0
  have hd := PV_L2C_NativeFold.fold_zero_decode xs hc
  have he : PV_L2C_NativeFold.fold xs 0=0 := decode_injective _ _ hc' h0 (by rw [hd,hz]; rfl)
  have hz' : wrap (0 : word)=aspis_core.field.M31.ZERO := rfl
  rw [← hz',source,he]
#print axioms zero_sum
end PV_L2C_ExtractedM31Fold
