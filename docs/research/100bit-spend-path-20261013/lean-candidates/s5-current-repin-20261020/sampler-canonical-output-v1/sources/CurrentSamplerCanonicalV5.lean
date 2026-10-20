import AspisR1Post25Sampler.Funs
import ExtractedMaskHornerStep
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1Post25SamplerCanonical
open AspisR1Post25Sampler
private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = .ok v) : ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
private theorem bind_ok_id {α : Type} (m : Result α) :
    (do let x ← m; Result.ok x) = m := by
  cases m <;> rfl
private def reduced (x : U32) : U32 := ⟨BitVec.umod x.bv (2147483647#u32).bv⟩
private theorem rem_success (x : U32) : (x % field.P : Result U32) = .ok (reduced x) := by
  unfold field.P
  rfl
private theorem reduced_val (x : U32) : (reduced x).val = x.val % 2147483647 := by
  change (x.bv % (2147483647#32)).toNat = x.bv.toNat % 2147483647
  rw [BitVec.toNat_umod]
  rfl
private theorem mod_result_bound (x y : U32) (h : (x % field.P : Result U32) = .ok y) : y.val < 2147483647 := by
  have he : reduced x = y := Result.ok.inj ((rem_success x).symm.trans h)
  rw [← he, reduced_val]
  exact Nat.mod_lt _ (by norm_num)
private theorem canonical_qm31_success_bounds (q out : field.QM31)
    (h : field.canonical_qm31 q = .ok out) :
    out.c0.a.val < 2147483647 ∧ out.c0.b.val < 2147483647 ∧
    out.c1.a.val < 2147483647 ∧ out.c1.b.val < 2147483647 := by
  unfold field.canonical_qm31 at h
  obtain ⟨a,ha,h⟩ := bind_success _ _ _ h
  obtain ⟨b,hb,h⟩ := bind_success _ _ _ h
  obtain ⟨c,hc,h⟩ := bind_success _ _ _ h
  obtain ⟨d,hd,h⟩ := bind_success _ _ _ h
  have hout : out = {c0 := {a := a, b := b}, c1 := {a := c, b := d}} := (Result.ok.inj h).symm
  rw [hout]
  exact ⟨mod_result_bound q.c0.a a (by simpa only [field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call, bind_ok_id] using ha),
    mod_result_bound q.c0.b b (by simpa only [field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call, bind_ok_id] using hb),
    mod_result_bound q.c1.a c (by simpa only [field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call, bind_ok_id] using hc),
    mod_result_bound q.c1.b d (by simpa only [field.canonical_qm31.closure.Insts.CoreOpsFunctionFnTupleM31M31.call, bind_ok_id] using hd)⟩
private theorem wide_new_success_bounds (q0 q1 : field.QM31) (out : field.WideExact)
    (h : field.WideExact.new q0 q1 = .ok out) :
    out.c0.c0.a.val < 2147483647 ∧ out.c0.c0.b.val < 2147483647 ∧
    out.c0.c1.a.val < 2147483647 ∧ out.c0.c1.b.val < 2147483647 ∧
    out.c1.c0.a.val < 2147483647 ∧ out.c1.c0.b.val < 2147483647 ∧
    out.c1.c1.a.val < 2147483647 ∧ out.c1.c1.b.val < 2147483647 := by
  unfold field.WideExact.new at h
  obtain ⟨a,ha,h⟩ := bind_success _ _ _ h
  obtain ⟨b,hb,h⟩ := bind_success _ _ _ h
  have hout : out = {c0 := a, c1 := b} := (Result.ok.inj h).symm
  rw [hout]
  obtain ⟨h00,h01,h02,h03⟩ := canonical_qm31_success_bounds q0 a ha
  obtain ⟨h10,h11,h12,h13⟩ := canonical_qm31_success_bounds q1 b hb
  exact ⟨h00,h01,h02,h03,h10,h11,h12,h13⟩

theorem decode8_success_bounds (digits : Array U32 8#usize) (out : field.WideExact)
    (h : sampler.decode8 digits = .ok out) :
    out.c0.c0.a.val < 2147483647 ∧ out.c0.c0.b.val < 2147483647 ∧
    out.c0.c1.a.val < 2147483647 ∧ out.c0.c1.b.val < 2147483647 ∧
    out.c1.c0.a.val < 2147483647 ∧ out.c1.c0.b.val < 2147483647 ∧
    out.c1.c1.a.val < 2147483647 ∧ out.c1.c1.b.val < 2147483647 := by
  let d0 := digits.val[0]'(by simpa [digits.property] using (show 0 < (8#usize).val by decide))
  let d1 := digits.val[1]'(by simpa [digits.property] using (show 1 < (8#usize).val by decide))
  let d2 := digits.val[2]'(by simpa [digits.property] using (show 2 < (8#usize).val by decide))
  let d3 := digits.val[3]'(by simpa [digits.property] using (show 3 < (8#usize).val by decide))
  let d4 := digits.val[4]'(by simpa [digits.property] using (show 4 < (8#usize).val by decide))
  let d5 := digits.val[5]'(by simpa [digits.property] using (show 5 < (8#usize).val by decide))
  let d6 := digits.val[6]'(by simpa [digits.property] using (show 6 < (8#usize).val by decide))
  let d7 := digits.val[7]'(by simpa [digits.property] using (show 7 < (8#usize).val by decide))
  have i0 : Array.index_usize digits 0#usize = .ok d0 := by
    simpa [d0] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok digits 0#usize (by decide)
  have i1 : Array.index_usize digits 1#usize = .ok d1 := by
    simpa [d1] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok digits 1#usize (by decide)
  have i2 : Array.index_usize digits 2#usize = .ok d2 := by
    simpa [d2] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok digits 2#usize (by decide)
  have i3 : Array.index_usize digits 3#usize = .ok d3 := by
    simpa [d3] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok digits 3#usize (by decide)
  have i4 : Array.index_usize digits 4#usize = .ok d4 := by
    simpa [d4] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok digits 4#usize (by decide)
  have i5 : Array.index_usize digits 5#usize = .ok d5 := by
    simpa [d5] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok digits 5#usize (by decide)
  have i6 : Array.index_usize digits 6#usize = .ok d6 := by
    simpa [d6] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok digits 6#usize (by decide)
  have i7 : Array.index_usize digits 7#usize = .ok d7 := by
    simpa [d7] using AspisR1.ExtractedMaskHornerStep.array_index_usize_ok digits 7#usize (by decide)
  have hs := h
  simp only [sampler.decode8, i0, i1, i2, i3, i4, i5, i6, i7,
    bind_tc_ok, field.CM31.new] at hs
  exact wide_new_success_bounds _ _ out hs
theorem ordinary_sample_success_bounds (block : Array U8 32#usize) (out : field.WideExact)
    (h : sampler.ordinary_sample block = .ok out) :
    out.c0.c0.a.val < 2147483647 ∧ out.c0.c0.b.val < 2147483647 ∧
    out.c0.c1.a.val < 2147483647 ∧ out.c0.c1.b.val < 2147483647 ∧
    out.c1.c0.a.val < 2147483647 ∧ out.c1.c0.b.val < 2147483647 ∧
    out.c1.c1.a.val < 2147483647 ∧ out.c1.c1.b.val < 2147483647 := by
  unfold sampler.ordinary_sample at h
  obtain ⟨pair, hlow, hdecode⟩ := bind_success _ _ _ h
  rcases pair with ⟨digits, high⟩
  exact decode8_success_bounds digits out hdecode

#print axioms decode8_success_bounds
#print axioms ordinary_sample_success_bounds
end AspisR1Post25SamplerCanonical
