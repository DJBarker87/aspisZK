import TerminalV4M31AddSubV1

/-! Reuses the GeneratedCM31Linear / GeneratedQM31Linear composition proofs
for freshly extracted functions on the full runtime. Canonical input premises
remain explicit; no verifier call-site or field-decoding conclusion is asserted. -/
set_option autoImplicit false

namespace AspisR1.TerminalV4TowerAdd

open Aeneas.Std Result

abbrev P : Nat := TerminalV4M31AddSub.P

def CanonicalCM (x : AspisR1SelectedMaskProbe.field.CM31) : Prop :=
  x.a.val < P ∧ x.b.val < P

def CanonicalQM (x : AspisR1SelectedMaskProbe.field.QM31) : Prop :=
  CanonicalCM x.c0 ∧ CanonicalCM x.c1

def wordsCM (x : AspisR1SelectedMaskProbe.field.CM31) : Nat × Nat :=
  (x.a.val, x.b.val)

def wordsQM (x : AspisR1SelectedMaskProbe.field.QM31) :
    (Nat × Nat) × (Nat × Nat) :=
  (wordsCM x.c0, wordsCM x.c1)

theorem current_cm_add_mod
    (x y : AspisR1SelectedMaskProbe.field.CM31)
    (hx : CanonicalCM x) (hy : CanonicalCM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.add x y = .ok z ∧
      CanonicalCM z ∧
      z.a.val = (x.a.val + y.a.val) % P ∧
      z.b.val = (x.b.val + y.b.val) % P := by
  obtain ⟨a, ea, va, ca⟩ :=
    AspisR1.TerminalV4M31AddSub.current_add_mod x.a y.a hx.1 hy.1
  obtain ⟨b, eb, vb, cb⟩ :=
    AspisR1.TerminalV4M31AddSub.current_add_mod x.b y.b hx.2 hy.2
  exact ⟨⟨a, b⟩,
    by simp only [AspisR1SelectedMaskProbe.field.CM31.add, ea, eb,
      bind_tc_ok],
    ⟨ca, cb⟩, va, vb⟩

theorem current_cm_sub_mod
    (x y : AspisR1SelectedMaskProbe.field.CM31)
    (hx : CanonicalCM x) (hy : CanonicalCM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.sub x y = .ok z ∧
      CanonicalCM z ∧
      z.a.val = (x.a.val + P - y.a.val) % P ∧
      z.b.val = (x.b.val + P - y.b.val) % P := by
  obtain ⟨a, ea, va, ca⟩ :=
    AspisR1.TerminalV4M31AddSub.current_sub_mod x.a y.a hx.1 hy.1
  obtain ⟨b, eb, vb, cb⟩ :=
    AspisR1.TerminalV4M31AddSub.current_sub_mod x.b y.b hx.2 hy.2
  exact ⟨⟨a, b⟩,
    by simp only [AspisR1SelectedMaskProbe.field.CM31.sub, ea, eb,
      bind_tc_ok],
    ⟨ca, cb⟩, va, vb⟩

theorem current_qm_add_mod
    (x y : AspisR1SelectedMaskProbe.field.QM31)
    (hx : CanonicalQM x) (hy : CanonicalQM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.add x y = .ok z ∧
      CanonicalQM z ∧
      wordsQM z =
        (((x.c0.a.val + y.c0.a.val) % P,
          (x.c0.b.val + y.c0.b.val) % P),
         ((x.c1.a.val + y.c1.a.val) % P,
          (x.c1.b.val + y.c1.b.val) % P)) := by
  obtain ⟨a, ea, ca, va, vb⟩ := current_cm_add_mod x.c0 y.c0 hx.1 hy.1
  obtain ⟨b, eb, cb, vc, vd⟩ := current_cm_add_mod x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.QM31.add, ea, eb,
      bind_tc_ok]
  · exact Prod.ext (Prod.ext va vb) (Prod.ext vc vd)

theorem current_qm_sub_mod
    (x y : AspisR1SelectedMaskProbe.field.QM31)
    (hx : CanonicalQM x) (hy : CanonicalQM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.sub x y = .ok z ∧
      CanonicalQM z ∧
      wordsQM z =
        (((x.c0.a.val + P - y.c0.a.val) % P,
          (x.c0.b.val + P - y.c0.b.val) % P),
         ((x.c1.a.val + P - y.c1.a.val) % P,
          (x.c1.b.val + P - y.c1.b.val) % P)) := by
  obtain ⟨a, ea, ca, va, vb⟩ := current_cm_sub_mod x.c0 y.c0 hx.1 hy.1
  obtain ⟨b, eb, cb, vc, vd⟩ := current_cm_sub_mod x.c1 y.c1 hx.2 hy.2
  refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.QM31.sub, ea, eb,
      bind_tc_ok]
  · exact Prod.ext (Prod.ext va vb) (Prod.ext vc vd)

#print axioms current_cm_add_mod
#print axioms current_cm_sub_mod
#print axioms current_qm_add_mod
#print axioms current_qm_sub_mod

end AspisR1.TerminalV4TowerAdd
