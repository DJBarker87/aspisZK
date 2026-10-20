import CurrentWideMulExactProduct
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1CurrentWide.Proof
private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {x : β} (h : Bind.bind r f = .ok x) :
    ∃ a, r = .ok a ∧ f a = .ok x := by
  cases r with
  | ok a => exact ⟨a,rfl,h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

theorem qm_sub_total_canonical (x y : field.QM31) (hx : CanonicalQM x) (hy : CanonicalQM y) :
    ∃ z, field.QM31.sub x y = .ok z ∧ CanonicalQM z := by
  obtain ⟨out,ho,hc⟩ := AspisR1CurrentWideMul.qm_sub_total (toQM x) (toQM y) hx hy
  have hm : (do let z ← field.QM31.sub x y; ok (toQM z)) = .ok out :=
    (qm_sub_same_minimal x y).trans ho
  cases hr : field.QM31.sub x y with
  | fail e => simp [hr] at hm
  | div => simp [hr] at hm
  | ok z =>
    rw [hr,bind_tc_ok] at hm
    have he : toQM z = out := Result.ok.inj hm
    refine ⟨z,rfl,?_⟩
    change AspisR1CurrentWideMul.CanonicalQM (toQM z)
    rw [he]
    exact hc

theorem qm_add_total_canonical (x y : field.QM31) (hx : CanonicalQM x) (hy : CanonicalQM y) :
    ∃ z, field.QM31.add x y = .ok z ∧ CanonicalQM z := by
  obtain ⟨out,ho,hc,_⟩ := AspisR1.ExtractedCurrentTowerAdd.current_qm_add_mod (toQM x) (toQM y) hx hy
  have hm : (do let z ← field.QM31.add x y; ok (toQM z)) = .ok out :=
    (qm_add_same x y).trans ho
  cases hr : field.QM31.add x y with
  | fail e => simp [hr] at hm
  | div => simp [hr] at hm
  | ok z =>
    rw [hr,bind_tc_ok] at hm
    have he : toQM z = out := Result.ok.inj hm
    refine ⟨z,rfl,?_⟩
    change AspisR1CurrentWideMul.CanonicalQM (toQM z)
    rw [he]
    exact hc

theorem qm_sub_success_canonical (x y z : field.QM31) (hx : CanonicalQM x) (hy : CanonicalQM y)
    (h : field.QM31.sub x y = .ok z) : CanonicalQM z := by
  obtain ⟨out,ho,hc⟩ := qm_sub_total_canonical x y hx hy
  have he : z = out := Result.ok.inj (h.symm.trans ho)
  rw [he]
  exact hc

theorem wide_sub_success_exact (x y z : E) (hx : CanonicalWide x) (hy : CanonicalWide y)
    (h : field.wide_exact.WideExact.sub x y = .ok z) :
    CanonicalWide z ∧ decodeWide z = decodeWide x - decodeWide y := by
  unfold field.wide_exact.WideExact.sub at h
  rcases bind_ok_inv h with ⟨a,ha,h⟩
  rcases bind_ok_inv h with ⟨b,hb,h⟩
  have he : ({c0:=a,c1:=b} : E) = z := Result.ok.inj h
  subst z
  refine ⟨⟨qm_sub_success_canonical x.c0 y.c0 a hx.1 hy.1 ha,
    qm_sub_success_canonical x.c1 y.c1 b hx.2 hy.2 hb⟩, ?_⟩
  apply QuadraticAlgebra.ext
  · exact qm_sub_exact x.c0 y.c0 a ha
  · exact qm_sub_exact x.c1 y.c1 b hb

theorem wide_sub_total_exact (x y : E) (hx : CanonicalWide x) (hy : CanonicalWide y) :
    ∃ z, field.wide_exact.WideExact.sub x y = .ok z ∧
      CanonicalWide z ∧ decodeWide z = decodeWide x - decodeWide y := by
  obtain ⟨lo,hlo,_⟩ := qm_sub_total_canonical x.c0 y.c0 hx.1 hy.1
  obtain ⟨hi,hhi,_⟩ := qm_sub_total_canonical x.c1 y.c1 hx.2 hy.2
  let z : E := ⟨lo,hi⟩
  have hz : field.wide_exact.WideExact.sub x y = .ok z := by
    simp only [field.wide_exact.WideExact.sub,hlo,hhi,bind_tc_ok,z]
  exact ⟨z,hz,wide_sub_success_exact x y z hx hy hz⟩

theorem wide_add_total_exact (x y : E) (hx : CanonicalWide x) (hy : CanonicalWide y) :
    ∃ z, field.wide_exact.WideExact.add x y = .ok z ∧
      CanonicalWide z ∧ decodeWide z = decodeWide x + decodeWide y := by
  obtain ⟨lo,hlo,_⟩ := qm_add_total_canonical x.c0 y.c0 hx.1 hy.1
  obtain ⟨hi,hhi,_⟩ := qm_add_total_canonical x.c1 y.c1 hx.2 hy.2
  let z : E := ⟨lo,hi⟩
  have hz : field.wide_exact.WideExact.add x y = .ok z := by
    simp only [field.wide_exact.WideExact.add,hlo,hhi,bind_tc_ok,z]
  exact ⟨z,hz,wide_add_success x y z hx hy hz⟩

#print axioms qm_sub_total_canonical
#print axioms qm_add_total_canonical
#print axioms qm_sub_success_canonical
#print axioms wide_sub_success_exact
#print axioms wide_sub_total_exact
#print axioms wide_add_total_exact
end AspisR1CurrentWide.Proof
