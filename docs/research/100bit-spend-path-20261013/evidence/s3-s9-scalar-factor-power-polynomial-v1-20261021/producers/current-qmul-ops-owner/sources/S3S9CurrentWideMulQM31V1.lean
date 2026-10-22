import KpowersCurrentQMSemanticsV1
import CurrentWideField

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9HelperP6PowerSemanticsV1

abbrev GW := AspisR1S9HelperP6.field.WideExact
abbrev CW := AspisR1CurrentWide.field.wide_exact.WideExact
abbrev ExactWide := AspisWideTower.WideExact

def helperToCurrentWide (x : GW) : CW :=
  ⟨helperToCurrentQM x.c0, helperToCurrentQM x.c1⟩

def currentToHelperWide (x : CW) : GW :=
  ⟨currentToHelperQM x.c0, currentToHelperQM x.c1⟩

/-- The source's canonical_qm31 projection, with its four checked U32
remainders in the same left-to-right order. -/
private def canonicalWord (x : Std.U32) : Result Std.U32 :=
  x % (2147483647#u32)

private def canonicalQM (x : AspisR1S9HelperP6.field.QM31) : Result AspisR1S9HelperP6.field.QM31 := do
  let a ← canonicalWord x.c0.a
  let b ← canonicalWord x.c0.b
  let c ← canonicalWord x.c1.a
  let d ← canonicalWord x.c1.b
  ok ⟨⟨a, b⟩, ⟨c, d⟩⟩

private theorem canonicalWord_id_of_bound (x : Std.U32)
    (hx : x.val < 2147483647) : canonicalWord x = .ok x := by
  obtain ⟨y, hy, hv⟩ :=
    Aeneas.Std.WP.spec_imp_exists
      (Aeneas.Std.UScalar.rem_spec x (y := 2147483647#u32) (by decide))
  have hval : y.val = x.val := by
    rw [hv]
    exact Nat.mod_eq_of_lt hx
  have heq : y = x := Aeneas.Std.UScalar.eq_of_val_eq hval
  simpa [canonicalWord] using hy.trans (congrArg Result.ok heq)

private theorem canonicalQM_id_of_canonical (q : AspisR1S9HelperP6.field.QM31)
    (hq : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q)) :
    canonicalQM q = .ok q := by
  have hq' :
      (q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647) ∧
      (q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647) := by
    change AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q) at hq
    simpa only [AspisR1CurrentWide.Proof.CanonicalQM,
      AspisR1CurrentWide.Proof.toQM,
      AspisR1CurrentWide.Proof.toCM,
      AspisR1.ExtractedCurrentQM31Exact.CurrentCanonicalQM,
      AspisR1.ExtractedCurrentQM31Tower.CurrentCanonicalQM,
      AspisR1.ExtractedCurrentTowerAdd.CanonicalQM,
      AspisR1.ExtractedCurrentTowerAdd.CanonicalCM,
      AspisR1.ExtractedCurrentTowerAdd.P,
      AspisR1.ExtractedCurrentM31AddSub.P,
      helperToCurrentQM] using hq
  obtain ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩ := hq'
  simp only [canonicalQM, canonicalWord_id_of_bound _ h00,
    canonicalWord_id_of_bound _ h01, canonicalWord_id_of_bound _ h10,
    canonicalWord_id_of_bound _ h11, bind_tc_ok]

@[simp] theorem currentToHelperWide_helperToCurrentWide (x : GW) :
    currentToHelperWide (helperToCurrentWide x) = x := by cases x; simp [helperToCurrentWide, currentToHelperWide]

@[simp] theorem helperToCurrentWide_currentToHelperWide (x : CW) :
    helperToCurrentWide (currentToHelperWide x) = x := by cases x; simp [helperToCurrentWide, currentToHelperWide]

/-- The source `WideExact::mul_qm31` operation, represented as its two QM31
multiplications over the selected current field operations. The Rust source
canonicalizes the right operand first; callers below require that operand to
already satisfy the selected canonical predicate. -/
def currentWideMulQM31 (x : GW) (q : AspisR1S9HelperP6.field.QM31) : Result GW := do
  let a ← AspisR1CurrentWide.field.QM31.mul (helperToCurrentQM x.c0) (helperToCurrentQM q)
  let b ← AspisR1CurrentWide.field.QM31.mul (helperToCurrentQM x.c1) (helperToCurrentQM q)
  ok (currentToHelperWide ⟨a, b⟩)

/-- Source-shaped `mul_qm31`: canonicalize the right operand, then multiply
both WideExact coordinates. -/
def currentWideMulQM31Source (x : GW) (q : AspisR1S9HelperP6.field.QM31) : Result GW := do
  let q' ← canonicalQM q
  currentWideMulQM31 x q'

theorem currentWideMulQM31Source_of_canonical (x : GW)
    (q : AspisR1S9HelperP6.field.QM31)
    (hq : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q)) :
    currentWideMulQM31Source x q = currentWideMulQM31 x q := by
  simp only [currentWideMulQM31Source, canonicalQM_id_of_canonical _ hq, bind_tc_ok]

private theorem bind_ok_inv {α β : Type} {r : Result α} {f : α → Result β}
    {z : β} (h : Bind.bind r f = .ok z) :
    ∃ a, r = .ok a ∧ f a = .ok z := by
  cases r with
  | ok a => exact ⟨a, rfl, h⟩
  | fail e => simp [Bind.bind] at h
  | div => simp [Bind.bind] at h

/-- Successful mixed multiplication preserves canonicality and decodes as
componentwise multiplication in the exact wide tower. This is the operation
law needed by scalar_factor; it does not instantiate the other FieldOps slots. -/
theorem currentWideMulQM31_success (x : GW) (q : AspisR1S9HelperP6.field.QM31)
    (z : GW)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (helperToCurrentWide x))
    (hq : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q))
    (h : currentWideMulQM31 x q = .ok z) :
    AspisR1CurrentWide.Proof.CanonicalWide (helperToCurrentWide z) ∧
      AspisR1CurrentWide.Proof.decodeWide (helperToCurrentWide z) =
        ⟨AspisR1CurrentWide.Proof.decodeQM (helperToCurrentQM x.c0) *
            AspisR1CurrentWide.Proof.decodeQM (helperToCurrentQM q),
          AspisR1CurrentWide.Proof.decodeQM (helperToCurrentQM x.c1) *
            AspisR1CurrentWide.Proof.decodeQM (helperToCurrentQM q)⟩ := by
  unfold currentWideMulQM31 at h
  rcases bind_ok_inv h with ⟨a, ha, h⟩
  rcases bind_ok_inv h with ⟨b, hb, h⟩
  have h' : currentToHelperWide ⟨a, b⟩ = z := Result.ok.inj h
  have hzc0 : helperToCurrentQM z.c0 = a := by
    have ht := congrArg helperToCurrentQM (congrArg (fun w : GW => w.c0) h'.symm)
    simpa [currentToHelperWide] using ht
  have hzc1 : helperToCurrentQM z.c1 = b := by
    have ht := congrArg helperToCurrentQM (congrArg (fun w : GW => w.c1) h'.symm)
    simpa [currentToHelperWide] using ht
  have hz : (⟨a, b⟩ : CW) = helperToCurrentWide z := by
    calc
      (⟨a, b⟩ : CW) = helperToCurrentWide (currentToHelperWide ⟨a, b⟩) :=
        (helperToCurrentWide_currentToHelperWide _).symm
      _ = helperToCurrentWide z := congrArg helperToCurrentWide h'
  have ha' := AspisR1CurrentWide.Proof.qm_mul_success
    (helperToCurrentQM x.c0) (helperToCurrentQM q) a hx.1 hq ha
  have hb' := AspisR1CurrentWide.Proof.qm_mul_success
    (helperToCurrentQM x.c1) (helperToCurrentQM q) b hx.2 hq hb
  constructor
  · refine ⟨?_, ?_⟩
    · change AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM z.c0)
      rw [hzc0]
      exact ha'.1
    · change AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM z.c1)
      rw [hzc1]
      exact hb'.1
  · unfold AspisR1CurrentWide.Proof.decodeWide
    rw [← hz]
    apply QuadraticAlgebra.ext
    · exact ha'.2
    · exact hb'.2

theorem currentWideMulQM31Source_success (x : GW)
    (q : AspisR1S9HelperP6.field.QM31) (z : GW)
    (hx : AspisR1CurrentWide.Proof.CanonicalWide (helperToCurrentWide x))
    (hq : AspisR1CurrentWide.Proof.CanonicalQM (helperToCurrentQM q))
    (h : currentWideMulQM31Source x q = .ok z) :
    AspisR1CurrentWide.Proof.CanonicalWide (helperToCurrentWide z) ∧
      AspisR1CurrentWide.Proof.decodeWide (helperToCurrentWide z) =
        ⟨AspisR1CurrentWide.Proof.decodeQM (helperToCurrentQM x.c0) *
            AspisR1CurrentWide.Proof.decodeQM (helperToCurrentQM q),
          AspisR1CurrentWide.Proof.decodeQM (helperToCurrentQM x.c1) *
            AspisR1CurrentWide.Proof.decodeQM (helperToCurrentQM q)⟩ := by
  have hcanonical := currentWideMulQM31Source_of_canonical x q hq
  have hmul : currentWideMulQM31 x q = .ok z := hcanonical.symm.trans h
  exact currentWideMulQM31_success x q z hx hq hmul

#print axioms currentWideMulQM31_success
#print axioms canonicalWord_id_of_bound
#print axioms canonicalQM_id_of_canonical
#print axioms currentWideMulQM31Source_of_canonical
#print axioms currentWideMulQM31Source_success

end AspisR1S9HelperP6PowerSemanticsV1
