import AspisR1ProducerRelease47.KernelCallers49
import AspisR1ProducerRelease47.Samples49
import R1Z.ProverCommitNativeQInverse49
/-! The actual half producer, not a supplied field constant. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitHalf49
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisV8R15.ExactTowerBase
open AspisR1.ExtractedCurrentQM31Exact (decode)

def word : U32 := ProverCommitInverse48.inverseWord 2#u32
def raw : Old.Q := ⟨⟨word,0#u32⟩,⟨0#u32,0#u32⟩⟩

theorem canonical : Canonical raw :=
  ⟨⟨ProverCommitInverse48.inverse_canonical _,by decide⟩,⟨by decide,by decide⟩⟩

theorem word_value : (word.val : M31Exact)=(2 : M31Exact)⁻¹ := by
  exact ProverCommitInverse48.inverse_decode 2#u32

theorem two_nonzero : (2 : M31Exact)≠0 := by
  intro he
  have hv := congrArg ZMod.val he
  change ZMod.val ((2:Nat) : ZMod AspisCircleGroupOrder.P)=ZMod.val 0 at hv
  rw [ZMod.val_natCast_of_lt (by decide : 2<AspisCircleGroupOrder.P),ZMod.val_zero] at hv
  omega

theorem half_plus : decode raw+decode raw=1 := by
  have ht : (2 : M31Exact)≠0 := two_nonzero
  have hi : (word.val : M31Exact)+(word.val : M31Exact)=1 := by
    rw [word_value,←two_mul,mul_inv_cancel₀ ht]
  apply QuadraticAlgebra.ext
  · apply QuadraticAlgebra.ext
    · exact hi
    · change (0 : M31Exact)+0=0;ring
  · apply QuadraticAlgebra.ext <;> change (0 : M31Exact)+0=0 <;> ring

theorem value : decode raw=(2 : QM31Exact)⁻¹ := by
  have ht : (2 : QM31Exact)≠0 := by
    intro he
    have h : (2 : M31Exact)=0 := congrArg (fun x : QM31Exact => x.re.re) he
    exact two_nonzero h
  apply mul_left_cancel₀ ht
  rw [mul_inv_cancel₀ ht,two_mul,half_plus]

theorem result : extras.half=ok (ProverCommitNativeQ48.source raw) := by
  have hi : inverse_ref 2#u32=ok word := by
    rw [ProverCommitInterpolationInverse48.source_inverse,ProverCommitInverse48.inverse_result]
    simp only [ne_eq,show (2#u32)≠0#u32 by decide,not_false_eq_true,massert,if_true,bind_tc_ok]
    rfl
  simp only [extras.half,hi,bind_tc_ok,field.CM31.from_m31,field.QM31.from_cm31,
    field.M31.ZERO,field.CM31.ZERO,ProverCommitNativeQ48.source,ProverCommitRelease47.convQ,
    ProverCommitRelease47.convC,fromQ,fromC,raw]

#print axioms canonical
#print axioms word_value
#print axioms two_nonzero
#print axioms half_plus
#print axioms value
#print axioms result
end R1Z.ProverCommitHalf49
