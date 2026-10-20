import AspisR1BatchedWeightsPushBodyBoundedV4

/-! Exact frozen row-update loop body, using the retained definitionally equal
M31 = U32 layout. See the packet's row-body-binding.json. This module proves
one selected iteration; the whole mutable-iterator loop and callers remain open. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace S8FrozenRow
open AspisR1BatchedWeightsExtraction
def verifier.power_limb_at
  (limbs : Array Std.U32 4#usize) (index : Std.Usize) : Result Std.U32 := do
  Array.index_usize limbs index

def verifier.residue_limb_at
  (row : Array Std.U64 4#usize) (index : Std.Usize) : Result Std.U64 := do
  Array.index_usize row index

def verifier.update_residue_row_loop0.body
  (limbs : Array Std.U32 4#usize) (iter : core.ops.range.Range Std.Usize)
  (row : Array Std.U64 4#usize) (basis : aspis_core.field.M31) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array Std.U64
    4#usize) × aspis_core.field.M31) (Array Std.U64 4#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done row)
  | some j =>
    let old ← verifier.residue_limb_at row j
    let limb ← verifier.power_limb_at limbs j
    let i ← lift (core.convert.num.FromU64U32.from limb)
    let i1 ← lift (core.convert.num.FromU64U32.from basis)
    let i2 ← i * i1
    let i3 ← old + i2
    let row1 ← Array.update row j i3
    ok (cont (iter1, row1, basis))

theorem row_step_total
    (limbs : Array Std.U32 4#usize) (iter : core.ops.range.Range Usize)
    (basis : aspis_core.field.M31) (j : Usize) (iterNext : core.ops.range.Range Usize)
    (limb : Std.U32) (old : Array Std.U64 4#usize)
    (previous : Std.U64)
    (terms : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some j, iterNext))
    (hj : j.val < 4)
    (hlimbRead : Array.index_usize limbs j = .ok limb)
    (hlimbBound : limb.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hraw : previous.val < 2^34 + (terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (hread : Array.index_usize old j = .ok previous) :
    ∃ product : Std.U64, ∃ updated : Array Std.U64 4#usize,
      (limb.val * basis.val) = product.val ∧
      verifier.update_residue_row_loop0.body limbs iter old basis =
        .ok (.cont (iterNext, updated, basis)) := by
  have h4 : (4#usize).val = 4 := by decide
  have hju : j.val < (4#usize).val := by simpa [h4] using hj
  let x : Std.U32 := limb
  have hx : x.val < AspisV8R17.RawReducer.P := by simpa [x] using hlimbBound
  have hreadLimbs : Array.index_usize limbs j = .ok x := by simpa [x] using hlimbRead
  let limb64 : Std.U64 := core.convert.num.FromU64U32.from x
  let basis64 : Std.U64 := core.convert.num.FromU64U32.from basis
  have hlimb64 : lift (core.convert.num.FromU64U32.from x) = .ok limb64 := by rfl
  have hbasis64 : lift (core.convert.num.FromU64U32.from basis) = .ok basis64 := by rfl
  have hprodLt : limb64.val * basis64.val < 2^64 := by
    change (core.convert.num.FromU64U32.from x).val *
      (core.convert.num.FromU64U32.from basis).val < 2^64
    rw [AspisR1.ExtractedCurrentCM31Mul.widen_value x,
      AspisR1.ExtractedCurrentCM31Mul.widen_value basis]
    have hP : AspisV8R17.RawReducer.P < 2^31 := by norm_num [AspisV8R17.RawReducer.P]
    have hx' : x.val < 2^31 := lt_trans hx hP
    have hb' : basis.val < 2^31 := lt_trans hbasis hP
    have hmulNat := Nat.mul_lt_mul_of_lt_of_lt hx' hb'
    norm_num at hmulNat
    omega
  obtain ⟨product, hmul, hprodVal⟩ := AspisR1.ExtractedCurrentReducerOps.mul_success limb64 basis64 hprodLt
  have hP : AspisV8R17.RawReducer.P = 2147483647 := by norm_num [AspisV8R17.RawReducer.P]
  have hcap : AspisR1BatchedAllPrefix.cap = 4611686009837453316 := by norm_num [AspisR1BatchedAllPrefix.cap]
  have hprodVal' : product.val = limb.val * basis.val := by
    change product.val = (core.convert.num.FromU64U32.from x).val *
      (core.convert.num.FromU64U32.from basis).val at hprodVal
    rw [AspisR1.ExtractedCurrentCM31Mul.widen_value x,
      AspisR1.ExtractedCurrentCM31Mul.widen_value basis] at hprodVal
    simpa [x] using hprodVal
  have hprodBound : product.val ≤ AspisR1BatchedAllPrefix.cap := by
    rw [hprodVal']
    have hx'' : limb.val ≤ 2147483646 := by rw [hP] at hlimbBound; omega
    have hb'' : basis.val ≤ 2147483646 := by rw [hP] at hbasis; omega
    rw [hcap]
    nlinarith [Nat.mul_le_mul hx'' hb'']
  have hsumLt : previous.val + product.val < 2^64 := by
    rw [hcap] at hraw hprodBound
    have hmod : terms.val % 4 < 4 := Nat.mod_lt _ (by decide)
    omega
  obtain ⟨sum, hadd, _hsumVal⟩ := AspisR1.ExtractedCurrentReducerOps.add_success previous product hsumLt
  have hidx : j.val < old.val.length := by simpa [old.property] using hju
  obtain ⟨updated, hupdate, _hset⟩ :=
    WP.spec_imp_exists (Array.update_spec old j sum hidx)
  refine ⟨product, updated, hprodVal'.symm, ?_⟩
  simp only [verifier.update_residue_row_loop0.body, verifier.residue_limb_at,
    verifier.power_limb_at, hnext, bind_tc_ok, hreadLimbs,
    hlimb64, hbasis64, hread]
  change (do
    let p ← UScalar.mul limb64 basis64
    let s ← UScalar.add previous p
    let r ← Array.update old j s
    ok (.cont (iterNext, r, basis))) = _
  rw [hmul]
  simp only [bind_tc_ok]
  rw [hadd]
  simp only [bind_tc_ok, hupdate]

#print axioms row_step_total
end S8FrozenRow
