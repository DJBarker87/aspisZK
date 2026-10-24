import AspisR1S9ProductionPairCutV1.Funs
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualSharedGuardSourceV1
abbrev Q := aspis_core.field.QM31
abbrev C := aspis_core.field.CM31
abbrev Cell := Array Q 4#usize
abbrev Row := Array Cell 5#usize
local instance (x y : C) : Decidable (x=y) := Classical.propDecidable _
local instance (x y : Q) : Decidable (x=y) := Classical.propDecidable _

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m = .ok a ∧ f a = .ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

theorem cm_eq_value (x y : C) :
    aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq x y = .ok (decide (x=y)) := by
  classical
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  by_cases ha : a=c <;> by_cases hb : b=d <;>
    simp_all [aspis_core.field.CM31.Insts.CoreCmpPartialEqCM31.eq,
      aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq]

theorem qm_eq_value (x y : Q) :
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq x y = .ok (decide (x=y)) := by
  classical
  rcases x with ⟨a,b⟩
  rcases y with ⟨c,d⟩
  by_cases ha : a=c <;> by_cases hb : b=d <;>
    simp_all [aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.eq,cm_eq_value]

theorem qm_ne_spec (x y : Q) :
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne x y ⦃ b => b ↔ x ≠ y ⦄ := by
  classical
  simp only [core.cmp.PartialEq.ne.default,qm_eq_value,bind_tc_ok,
    WP.spec_ok,decide_eq_true_eq]

theorem cell_eq_true (a b : Cell)
    (h : core.array.equality.PartialEqArray.eq
      aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 a b = .ok true) : a=b := by
  have hs := core.slice.cmp.PartialEqSlice.eq_homo_spec
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 a.to_slice b.to_slice qm_ne_spec
  change WP.spec (core.array.equality.PartialEqArray.eq
    aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31 a b)
    (fun v => v ↔ a.to_slice=b.to_slice) at hs
  rw [h] at hs
  have he : a.to_slice=b.to_slice := (WP.spec_ok.mp hs).mp rfl
  apply Subtype.ext
  exact congrArg (fun s : Slice Q => s.val) he

/-- The actual accepted guard compares the same receiver rows and proves raw
four-word-cell equality at dimensions2 and3. No canonicality or model equality
premise is used, and the independent dimension4 remains unconstrained. -/
theorem guard_true_raw_cells (w : weights.Weights) (folds : Usize)
    (h : weights.shared_two_point_guard w folds = .ok true) :
    ∃ (r0 r2 : Row) (d02 d22 d03 d23 : Cell),
      Array.index_usize w.factors 0#usize = .ok r0 ∧
      Array.index_usize w.factors 2#usize = .ok r2 ∧
      Array.index_usize r0 2#usize = .ok d02 ∧
      Array.index_usize r2 2#usize = .ok d22 ∧
      Array.index_usize r0 3#usize = .ok d03 ∧
      Array.index_usize r2 3#usize = .ok d23 ∧ d02=d22 ∧ d03=d23 := by
  unfold weights.shared_two_point_guard at h
  obtain ⟨b,hb,h⟩ := bind_success _ _ _ h
  cases b with
  | false => cases h
  | true =>
    simp only [↓reduceIte] at h
    split at h
    · obtain ⟨r0,hr0,h⟩ := bind_success _ _ _ h
      obtain ⟨d02,hd02,h⟩ := bind_success _ _ _ h
      obtain ⟨r2,hr2,h⟩ := bind_success _ _ _ h
      obtain ⟨d22,hd22,h⟩ := bind_success _ _ _ h
      obtain ⟨b,hb,h⟩ := bind_success _ _ _ h
      cases b with
      | false => cases h
      | true =>
        simp only [↓reduceIte] at h
        obtain ⟨d03,hd03,h⟩ := bind_success _ _ _ h
        obtain ⟨d23,hd23,h⟩ := bind_success _ _ _ h
        exact ⟨r0,r2,d02,d22,d03,d23,hr0,hr2,hd02,hd22,hd03,hd23,
          cell_eq_true _ _ hb,cell_eq_true _ _ h⟩
    · cases h

#print axioms cm_eq_value
#print axioms qm_eq_value
#print axioms qm_ne_spec
#print axioms cell_eq_true
#print axioms guard_true_raw_cells
end AspisR1S9ActualSharedGuardSourceV1
