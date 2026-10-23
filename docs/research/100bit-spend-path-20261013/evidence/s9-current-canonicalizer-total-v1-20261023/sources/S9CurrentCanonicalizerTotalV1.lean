import S3S9GeneratedWideMulQM31V2
import CurrentWideField

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9CurrentCanonicalizerTotalV1

abbrev CurQ := AspisR1CurrentWide.field.QM31

private def reduced (x : Std.U32) : Std.U32 :=
  ⟨BitVec.umod x.bv (2147483647#u32).bv⟩

private theorem rem_success (x : Std.U32) :
    (x % AspisR1CurrentWide.field.P : Result Std.U32) = .ok (reduced x) := by
  unfold AspisR1CurrentWide.field.P
  rfl

private theorem reduced_val (x : Std.U32) :
    (reduced x).val = x.val % 2147483647 := by
  change (x.bv % (2147483647#32)).toNat = x.bv.toNat % 2147483647
  rw [BitVec.toNat_umod]
  rfl

private theorem rem_bound (x y : Std.U32)
    (h : (x % AspisR1CurrentWide.field.P : Result Std.U32) = .ok y) :
    y.val < 2147483647 := by
  have he : reduced x = y := Result.ok.inj ((rem_success x).symm.trans h)
  rw [← he, reduced_val]
  exact Nat.mod_lt _ (by decide)

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem bind_ok_id {α : Type} (m : Result α) :
    (do let x ← m; Result.ok x) = m := by
  cases m <;> rfl

private theorem canonicalizer_bounds (q z : CurQ)
    (h : AspisR1CurrentWide.field.wide_exact.canonical_qm31 q = .ok z) :
    z.c0.a.val < 2147483647 ∧ z.c0.b.val < 2147483647 ∧
    z.c1.a.val < 2147483647 ∧ z.c1.b.val < 2147483647 := by
  unfold AspisR1CurrentWide.field.wide_exact.canonical_qm31 at h
  obtain ⟨a, ha, h⟩ := bind_success _ _ _ h
  obtain ⟨b, hb, h⟩ := bind_success _ _ _ h
  obtain ⟨c, hc, h⟩ := bind_success _ _ _ h
  obtain ⟨d, hd, h⟩ := bind_success _ _ _ h
  have hout : z = { c0 := { a := a, b := b }, c1 := { a := c, b := d } } :=
    Result.ok.inj h.symm
  rw [hout]
  refine ⟨rem_bound q.c0.a a ?_, rem_bound q.c0.b b ?_,
    rem_bound q.c1.a c ?_, rem_bound q.c1.b d ?_⟩
  · simpa only [AspisR1CurrentWide.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
      bind_ok_id] using ha
  · simpa only [AspisR1CurrentWide.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
      bind_ok_id] using hb
  · simpa only [AspisR1CurrentWide.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
      bind_ok_id] using hc
  · simpa only [AspisR1CurrentWide.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call,
      bind_ok_id] using hd

theorem canonicalizer_total_canonical (q : CurQ) :
    ∃ z, AspisR1CurrentWide.field.wide_exact.canonical_qm31 q = .ok z ∧
      AspisR1CurrentWide.Proof.CanonicalQM z := by
  let z : CurQ := ⟨⟨reduced q.c0.a, reduced q.c0.b⟩,
    ⟨reduced q.c1.a, reduced q.c1.b⟩⟩
  have hcall (x : Std.U32) :
      AspisR1CurrentWide.field.wide_exact.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call () x =
        .ok (reduced x) := by
    change (do let v ← x % AspisR1CurrentWide.field.P; Result.ok v) = .ok (reduced x)
    rw [rem_success]
    rfl
  refine ⟨z, ?_, ?_⟩
  · unfold AspisR1CurrentWide.field.wide_exact.canonical_qm31
    simp only [hcall, bind_tc_ok]
    rfl
  · change (z.c0.a.val < 2147483647 ∧ z.c0.b.val < 2147483647) ∧
      (z.c1.a.val < 2147483647 ∧ z.c1.b.val < 2147483647)
    simp only [z, reduced_val]
    exact ⟨⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩,
      ⟨Nat.mod_lt _ (by decide), Nat.mod_lt _ (by decide)⟩⟩

#print axioms canonicalizer_bounds
#print axioms canonicalizer_total_canonical

end AspisR1S9CurrentCanonicalizerTotalV1
