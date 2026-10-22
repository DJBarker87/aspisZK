import CurrentWideField
import CurrentWideMulCanonical
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
abbrev MinimalWide := AspisR1CurrentWideMul.field.wide_exact.WideExact
def toMinimalWide (x : E) : MinimalWide := ⟨toQM x.c0,toQM x.c1⟩

theorem qm_sub_same_minimal (x y : field.QM31) :
    (do let z ← field.QM31.sub x y; ok (toQM z)) =
      AspisR1CurrentWideMul.field.QM31.sub (toQM x) (toQM y) := by
  unfold field.QM31.sub AspisR1CurrentWideMul.field.QM31.sub
  simp only [toQM,AspisR1CurrentWideMul.field.cm.CM31.sub,
    ←cm_sub_same,bind_assoc_eq,bind_tc_ok]

theorem mul_u_same_minimal (x : field.QM31) :
    (do let z ← field.wide_exact.mul_u x; ok (toQM z)) =
      AspisR1CurrentWideMul.field.wide_exact.mul_u (toQM x) := by
  unfold field.wide_exact.mul_u AspisR1CurrentWideMul.field.wide_exact.mul_u
  simp only [toQM,AspisR1CurrentWideMul.field.mul_by_r,
    ←mul_by_r_same,bind_assoc_eq,bind_tc_ok]

theorem wide_mul_same_minimal (x y : E) :
    (do let z ← field.wide_exact.WideExact.mul x y; ok (toMinimalWide z)) =
      AspisR1CurrentWideMul.field.wide_exact.WideExact.mul (toMinimalWide x) (toMinimalWide y) := by
  unfold field.wide_exact.WideExact.mul AspisR1CurrentWideMul.field.wide_exact.WideExact.mul
  simp only [toMinimalWide,AspisR1CurrentWideMul.field.QM31.mul,
    AspisR1CurrentWideMul.field.QM31.add,
    ←qm_mul_same,←qm_add_same,←qm_sub_same_minimal,←mul_u_same_minimal,
    bind_assoc_eq,bind_tc_ok]

theorem wide_mul_source_success_canonical (x y z : E)
    (hx : CanonicalWide x) (hy : CanonicalWide y)
    (h : field.wide_exact.WideExact.mul x y = .ok z) : CanonicalWide z := by
  have hx' : AspisR1CurrentWideMul.CanonicalWide (toMinimalWide x) := hx
  have hy' : AspisR1CurrentWideMul.CanonicalWide (toMinimalWide y) := hy
  obtain ⟨out,ho,hc⟩ := AspisR1CurrentWideMul.wide_mul_total_canonical
    (toMinimalWide x) (toMinimalWide y) hx' hy'
  have hm := wide_mul_same_minimal x y
  rw [h,bind_tc_ok] at hm
  have he : toMinimalWide z = out := Result.ok.inj (hm.trans ho)
  change AspisR1CurrentWideMul.CanonicalWide (toMinimalWide z)
  rw [he]
  exact hc


theorem wide_mul_source_total_canonical (x y : E)
    (hx : CanonicalWide x) (hy : CanonicalWide y) :
    ∃ z, field.wide_exact.WideExact.mul x y = .ok z ∧ CanonicalWide z := by
  have hx' : AspisR1CurrentWideMul.CanonicalWide (toMinimalWide x) := hx
  have hy' : AspisR1CurrentWideMul.CanonicalWide (toMinimalWide y) := hy
  obtain ⟨out,ho,_⟩ := AspisR1CurrentWideMul.wide_mul_total_canonical
    (toMinimalWide x) (toMinimalWide y) hx' hy'
  have hm : (do let z ← field.wide_exact.WideExact.mul x y; ok (toMinimalWide z)) = .ok out :=
    (wide_mul_same_minimal x y).trans ho
  cases hr : field.wide_exact.WideExact.mul x y with
  | fail e => simp [hr] at hm
  | div => simp [hr] at hm
  | ok z =>
    exact ⟨z,rfl,wide_mul_source_success_canonical x y z hx hy hr⟩

#print axioms qm_sub_same_minimal
#print axioms mul_u_same_minimal
#print axioms wide_mul_same_minimal
#print axioms wide_mul_source_total_canonical
#print axioms wide_mul_source_success_canonical
end AspisR1CurrentWide.Proof
