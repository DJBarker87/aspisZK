import CurrentFoldArithmeticABI
import CurrentWideProduct
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof

theorem current_fold_sub (x y z : FoldE) (hx : CanonicalFold x) (hy : CanonicalFold y)
    (h : currentFoldOps.sub x y = .ok z) :
    CanonicalFold z ∧ decodeFold z=decodeFold x-decodeFold y := by
  obtain ⟨out,ho,hz⟩ := runBinary_success field.wide_exact.WideExact.sub x y z h
  have hr := wide_sub_success (ofFoldE x) (ofFoldE y) out hx hy ho
  change CanonicalWide (ofFoldE z) ∧ decodeWide (ofFoldE z)=decodeWide (ofFoldE x)-decodeWide (ofFoldE y)
  rw [hz]
  exact hr

theorem current_fold_mul (x y z : FoldE) (hx : CanonicalFold x) (hy : CanonicalFold y)
    (h : currentFoldOps.mul x y = .ok z) :
    CanonicalFold z ∧ decodeFold z=decodeFold x*decodeFold y := by
  obtain ⟨out,ho,hz⟩ := runBinary_success field.wide_exact.WideExact.mul x y z h
  have hr := wide_mul_success (ofFoldE x) (ofFoldE y) out hx hy ho
  change CanonicalWide (ofFoldE z) ∧ decodeWide (ofFoldE z)=decodeWide (ofFoldE x)*decodeWide (ofFoldE y)
  rw [hz]
  exact hr

theorem current_fold_baseMul (x y z : U32)
    (h : currentFoldOps.baseMul x y = .ok z) :
    z.val<2147483647 ∧ R17CurrentM31Semantics.decode z =
      R17CurrentM31Semantics.decode x*R17CurrentM31Semantics.decode y := by
  change field.M31.mul x y = .ok z at h
  rw [m31_mul_same] at h
  obtain ⟨out,ho,_,hc⟩ := AspisR1.ExtractedCurrentReducer.current_mul_mod x y
  have he : out=z := Result.ok.inj (ho.symm.trans h)
  exact ⟨by simpa only [he] using hc,R17CurrentM31Semantics.current_mul_decode x y z h⟩

#print axioms current_fold_sub
#print axioms current_fold_mul
#print axioms current_fold_baseMul
end AspisR1CurrentWide.Proof
