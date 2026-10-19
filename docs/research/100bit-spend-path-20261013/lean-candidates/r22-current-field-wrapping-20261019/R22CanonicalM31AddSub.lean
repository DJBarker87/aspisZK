import CheckedWrappingScalarAgreement
import ExtractedCurrentM31AddSub
import ExtractedCurrentReducerOps

/-! R22: exact equality of the extracted checked M31 add/sub and the same
source expressions under wrapping primitives, for canonical inputs. This
supplies the required direction on this domain, not for a whole verifier. -/
set_option autoImplicit false
namespace AspisR1.R22CanonicalM31AddSub
open Aeneas Aeneas.Std Result
open CheckedWrappingScalarAgreement
abbrev M := AspisR1Qm31ArithmeticProbe.field.M31
abbrev sourceP := AspisR1Qm31ArithmeticProbe.field.P
abbrev P : Nat := 2147483647

#print AspisR1Qm31ArithmeticProbe.field.P
private theorem sourceP_value : sourceP.val = P := by
  change AspisR1Qm31ArithmeticProbe.field.P.val = 2147483647
  simp [AspisR1Qm31ArithmeticProbe.field.P]

private theorem result_right_unit (r : Result U32) :
    (do let z ← r; ok z) = r := by cases r <;> rfl

def wrappingFinish (n : U32) : U32 :=
  if n ≥ sourceP then UScalar.wrapping_sub n sourceP else n

def checkedFinish (n : U32) : Result U32 :=
  if n ≥ sourceP then do let z ← UScalar.sub n sourceP; ok z else ok n

theorem checkedFinish_eq (n : U32) : checkedFinish n = ok (wrappingFinish n) := by
  by_cases h : n ≥ sourceP
  · have hle : sourceP.val ≤ n.val := h
    obtain ⟨z,hz,_⟩ := ExtractedCurrentReducerOps.sub_success n sourceP hle
    have hw := (sub_success_agrees n sourceP z hz).1
    simp only [checkedFinish,wrappingFinish,h,if_pos,hz,bind_tc_ok,hw]
  · simp only [checkedFinish,wrappingFinish,h,if_false]

def wrappingAdd (x y : M) : M := wrappingFinish (UScalar.wrapping_add x y)
def wrappingSub (x y : M) : M :=
  wrappingFinish (UScalar.wrapping_sub (UScalar.wrapping_add x sourceP) y)

theorem canonical_add_agrees (x y : M) (hx : x.val < P) (hy : y.val < P) :
    AspisR1Qm31ArithmeticProbe.field.M31.add x y = ok (wrappingAdd x y) := by
  have hP : P = 2147483647 := rfl
  have hbound : x.val+y.val < 2^32 := by omega
  obtain ⟨s,hs,_⟩ := ExtractedCurrentReducerOps.tryMk_success (ty := .U32)
    (x.val+y.val) hbound
  have hs' : UScalar.add x y = ok s := hs
  have hw := (add_success_agrees x y s hs').1
  have hbody : AspisR1Qm31ArithmeticProbe.field.M31.add x y =
      (do let n ← UScalar.add x y; checkedFinish n) := rfl
  rw [hbody,hs']
  simp only [bind_tc_ok,wrappingAdd,hw,checkedFinish_eq]

theorem canonical_sub_agrees (x y : M) (hx : x.val < P) (hy : y.val < P) :
    AspisR1Qm31ArithmeticProbe.field.M31.sub x y = ok (wrappingSub x y) := by
  have hP : P = 2147483647 := rfl
  have hbound : x.val+sourceP.val < 2^32 := by rw [sourceP_value]; omega
  obtain ⟨s,hs,hsv⟩ := ExtractedCurrentReducerOps.tryMk_success (ty := .U32)
    (x.val+sourceP.val) hbound
  have hs' : UScalar.add x sourceP = ok s := hs
  have hwadd := (add_success_agrees x sourceP s hs').1
  have hle : y.val ≤ s.val := by rw [hsv,sourceP_value]; omega
  obtain ⟨n,hn,_⟩ := ExtractedCurrentReducerOps.sub_success s y hle
  have hwsub := (sub_success_agrees s y n hn).1
  have hbody : AspisR1Qm31ArithmeticProbe.field.M31.sub x y =
      (do let s ← UScalar.add x sourceP; let n ← UScalar.sub s y; checkedFinish n) := rfl
  rw [hbody,hs']
  simp only [bind_tc_ok,hn,wrappingSub,hwadd,hwsub,checkedFinish_eq]

theorem wrapping_add_canonical (x y : M) (hx : x.val < P) (hy : y.val < P) :
    (wrappingAdd x y).val < P := by
  obtain ⟨z,hz,_,hc⟩ := ExtractedCurrentM31AddSub.current_add_mod x y hx hy
  rw [canonical_add_agrees x y hx hy] at hz
  exact Result.ok.inj hz ▸ hc

theorem wrapping_sub_canonical (x y : M) (hx : x.val < P) (hy : y.val < P) :
    (wrappingSub x y).val < P := by
  obtain ⟨z,hz,_,hc⟩ := ExtractedCurrentM31AddSub.current_sub_mod x y hx hy
  rw [canonical_sub_agrees x y hx hy] at hz
  exact Result.ok.inj hz ▸ hc

#print axioms canonical_add_agrees
#print axioms canonical_sub_agrees
#print axioms wrapping_add_canonical
#print axioms wrapping_sub_canonical
end AspisR1.R22CanonicalM31AddSub
