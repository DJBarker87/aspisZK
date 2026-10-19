import TerminalV4CM31MulCurrent
import TerminalV4TowerAddV2

/-! Reuses the prior GeneratedMulByR and GeneratedQM31Products proof routes
for current extracted functions. This proves canonical modular word formulas,
not the verifier caller or the decoded exact-field correspondence. -/
set_option autoImplicit false

namespace AspisR1.TerminalV4QM31MulCurrent

open Aeneas.Std Result

abbrev P : Nat := TerminalV4TowerAdd.P
abbrev WordPair := Nat × Nat

def addWords (x y : WordPair) : WordPair :=
  ((x.1 + y.1) % P, (x.2 + y.2) % P)

def subWords (x y : WordPair) : WordPair :=
  ((x.1 + P - y.1) % P, (x.2 + P - y.2) % P)

def mulWords (x y : WordPair) : WordPair :=
  (((x.1 * y.1) % P + P - (x.2 * y.2) % P) % P,
   ((((x.1 + x.2) * (y.1 + y.2)) % P + P -
       (x.1 * y.1) % P) % P + P - (x.2 * y.2) % P) % P)

def rWords (x : WordPair) : WordPair :=
  (((x.1 + x.1) % P + P - x.2) % P,
   (x.1 + (x.2 + x.2) % P) % P)

def qmMulWords (x y : WordPair × WordPair) :=
  let m0 := mulWords x.1 y.1
  let m1 := mulWords x.2 y.2
  (addWords m0 (rWords m1),
   subWords (subWords (mulWords (addWords x.1 x.2)
     (addWords y.1 y.2)) m0) m1)

private def wordsCM (x : AspisR1SelectedMaskProbe.field.CM31) : WordPair :=
  (x.a.val, x.b.val)

def wordsQM (x : AspisR1SelectedMaskProbe.field.QM31) :
    WordPair × WordPair :=
  (wordsCM x.c0, wordsCM x.c1)

private theorem cm_add_words
    (x y : AspisR1SelectedMaskProbe.field.CM31)
    (hx : AspisR1.TerminalV4TowerAdd.CanonicalCM x)
    (hy : AspisR1.TerminalV4TowerAdd.CanonicalCM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.add x y = .ok z ∧
      AspisR1.TerminalV4TowerAdd.CanonicalCM z ∧
      wordsCM z = addWords (wordsCM x) (wordsCM y) := by
  obtain ⟨z, ez, cz, va, vb⟩ :=
    AspisR1.TerminalV4TowerAdd.current_cm_add_mod x y hx hy
  exact ⟨z, ez, cz, Prod.ext va vb⟩

private theorem cm_sub_words
    (x y : AspisR1SelectedMaskProbe.field.CM31)
    (hx : AspisR1.TerminalV4TowerAdd.CanonicalCM x)
    (hy : AspisR1.TerminalV4TowerAdd.CanonicalCM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.sub x y = .ok z ∧
      AspisR1.TerminalV4TowerAdd.CanonicalCM z ∧
      wordsCM z = subWords (wordsCM x) (wordsCM y) := by
  obtain ⟨z, ez, cz, va, vb⟩ :=
    AspisR1.TerminalV4TowerAdd.current_cm_sub_mod x y hx hy
  exact ⟨z, ez, cz, Prod.ext va vb⟩

private theorem cm_mul_words
    (x y : AspisR1SelectedMaskProbe.field.CM31)
    (hx : AspisR1.TerminalV4TowerAdd.CanonicalCM x)
    (hy : AspisR1.TerminalV4TowerAdd.CanonicalCM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.CM31.mul x y = .ok z ∧
      AspisR1.TerminalV4TowerAdd.CanonicalCM z ∧
      wordsCM z = mulWords (wordsCM x) (wordsCM y) := by
  obtain ⟨z, ez, cz, va, vb⟩ :=
    AspisR1.TerminalV4CM31MulCurrent.current_mul_words x y hx hy
  exact ⟨z, ez, cz, Prod.ext va vb⟩

private theorem cm_r_words
    (x : AspisR1SelectedMaskProbe.field.CM31)
    (hx : AspisR1.TerminalV4TowerAdd.CanonicalCM x) :
    ∃ z, AspisR1SelectedMaskProbe.field.mul_by_r x = .ok z ∧
      AspisR1.TerminalV4TowerAdd.CanonicalCM z ∧
      wordsCM z = rWords (wordsCM x) := by
  obtain ⟨a2, ea2, va2, ca2⟩ :=
    AspisR1.TerminalV4M31AddSub.current_add_mod x.a x.a hx.1 hx.1
  obtain ⟨a, ea, va, ca⟩ :=
    AspisR1.TerminalV4M31AddSub.current_sub_mod a2 x.b ca2 hx.2
  obtain ⟨b2, eb2, vb2, cb2⟩ :=
    AspisR1.TerminalV4M31AddSub.current_add_mod x.b x.b hx.2 hx.2
  obtain ⟨b, eb, vb, cb⟩ :=
    AspisR1.TerminalV4M31AddSub.current_add_mod x.a b2 hx.1 cb2
  refine ⟨⟨a, b⟩, ?_, ⟨ca, cb⟩, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.mul_by_r,
      AspisR1SelectedMaskProbe.field.M31.double,
      ea2, ea, eb2, eb, bind_tc_ok]
  · change (a.val, b.val) = rWords (wordsCM x)
    simp only [rWords, wordsCM]
    exact Prod.ext (by simpa only [va2] using va)
      (by simpa only [vb2] using vb)

theorem current_qm_mul_words
    (x y : AspisR1SelectedMaskProbe.field.QM31)
    (hx : AspisR1.TerminalV4TowerAdd.CanonicalQM x)
    (hy : AspisR1.TerminalV4TowerAdd.CanonicalQM y) :
    ∃ z, AspisR1SelectedMaskProbe.field.QM31.mul x y = .ok z ∧
      AspisR1.TerminalV4TowerAdd.CanonicalQM z ∧
      wordsQM z = qmMulWords (wordsQM x) (wordsQM y) := by
  obtain ⟨m0, e0, c0, v0⟩ := cm_mul_words x.c0 y.c0 hx.1 hy.1
  obtain ⟨m1, e1, c1, v1⟩ := cm_mul_words x.c1 y.c1 hx.2 hy.2
  obtain ⟨a, ea, ca, va⟩ := cm_add_words x.c0 x.c1 hx.1 hx.2
  obtain ⟨b, eb, cb, vb⟩ := cm_add_words y.c0 y.c1 hy.1 hy.2
  obtain ⟨m2, e2, c2, v2⟩ := cm_mul_words a b ca cb
  obtain ⟨r, er, cr, vr⟩ := cm_r_words m1 c1
  obtain ⟨lo, el, cl, vl⟩ := cm_add_words m0 r c0 cr
  obtain ⟨d, ed, cd, vd⟩ := cm_sub_words m2 m0 c2 c0
  obtain ⟨hi, eh, ch, vh⟩ := cm_sub_words d m1 cd c1
  refine ⟨⟨lo, hi⟩, ?_, ⟨cl, ch⟩, ?_⟩
  · simp only [AspisR1SelectedMaskProbe.field.QM31.mul,
      e0, e1, ea, eb, e2, er, el, ed, eh, bind_tc_ok]
  · change (wordsCM lo, wordsCM hi) = _
    rw [vl, vh, vd, vr, v2, va, vb, v0, v1]
    rfl

#print axioms current_qm_mul_words

end AspisR1.TerminalV4QM31MulCurrent
