import CurrentWideQMBridge
import ExtractedCurrentQM31Exact
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
abbrev ExactQM := AspisR1.ExtractedCurrentQM31Exact.QM31Exact
def CanonicalQM (x : field.QM31) : Prop :=
  AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM (toQM x)
def decodeQM (x : field.QM31) : ExactQM :=
  AspisR1.ExtractedCurrentQM31Exact.decode (toQM x)

theorem qm_add_success (x y z : field.QM31) (hx : CanonicalQM x) (hy : CanonicalQM y)
    (h : field.QM31.add x y = .ok z) :
    CanonicalQM z ∧ decodeQM z = decodeQM x + decodeQM y := by
  obtain ⟨out,ho,hc,hd⟩ := AspisR1.ExtractedCurrentQM31Exact.current_qm_add_exact (toQM x) (toQM y) hx hy
  have hm := qm_add_same x y
  rw [h,bind_tc_ok] at hm
  have he : toQM z=out := Result.ok.inj (hm.trans ho)
  constructor
  · change AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM (toQM z)
    rw [he]; exact hc
  · unfold decodeQM
    rw [he]; exact hd

theorem qm_mul_success (x y z : field.QM31) (hx : CanonicalQM x) (hy : CanonicalQM y)
    (h : field.QM31.mul x y = .ok z) :
    CanonicalQM z ∧ decodeQM z = decodeQM x * decodeQM y := by
  obtain ⟨out,ho,hc,hd⟩ := AspisR1.ExtractedCurrentQM31Exact.current_qm_mul_exact (toQM x) (toQM y) hx hy
  have hm := qm_mul_same x y
  rw [h,bind_tc_ok] at hm
  have he : toQM z=out := Result.ok.inj (hm.trans ho)
  constructor
  · change AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM (toQM z)
    rw [he]; exact hc
  · unfold decodeQM
    rw [he]; exact hd

#print axioms qm_add_success
#print axioms qm_mul_success
end AspisR1CurrentWide.Proof
