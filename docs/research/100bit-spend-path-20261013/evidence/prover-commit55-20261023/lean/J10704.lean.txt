import R1Z.ProverCommitEncoderGuard55
import R1Z.ProverCommitEncoderGenericEval54
/-! The length-guarded computation returns the exact polynomial value and is
canonical; the guard and proof-fuel assertions are discharged. -/
set_option autoImplicit false
namespace R1Z.ProverCommitEncoderGuardValue55
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitEncoderCollect54 ProverCommitEncoderEval54
open ProverCommitEncoderGenericEval54
theorem exact_result {E K : Type} [CommRing K] (inst : scalar.CodeField E)
    (valid : E → Prop) (decode : E → K) (nv : U32 → K) (ops : Arithmetic inst valid decode nv)
    (h : Nat) (hh : h≤8) (height depth : Usize)
    (hheight : height.val=h) (hdepth : depth.val+h≤9)
    (f : Nat → E) (hf : ∀ i, i<2^h → valid (f i))
    (c : Slice E) (hc : c.val=List.ofFn (fun i : Fin (2^h) => f i.val))
    (p : Nat → U32) (hp : ∀ i, i<9 → (p i).val<2147483647) :
    ∃ z : E, guarded55.eval_rec inst c depth height (nodes p)=ok (z) ∧
      valid z ∧ decode z=ProverCommitEncoderMath54.evaluate h (fun i => decode (f i)) (fun i => nv (p i)) depth.val := by
  rw [ProverCommitEncoderGuard55.equivalent inst h hh height depth hheight c
    (by rw [hc,List.length_ofFn])]
  exact ProverCommitEncoderGenericEval54.exact_result inst valid decode nv ops
    h hh height depth hheight hdepth f hf c hc p hp

#print axioms exact_result
end R1Z.ProverCommitEncoderGuardValue55
