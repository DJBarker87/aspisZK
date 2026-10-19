import AspisR1BatchedWeightsPushBodyStepV7
import ExtractedCurrentCM31Mul
import ExtractedCurrentReducerOps
import AspisR1BatchedAllPrefix
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
open Aeneas Aeneas.Std Result WP
namespace AspisR1BatchedWeightsPushBodyValueStepV1
open AspisR1BatchedWeightsExtraction
abbrev BW := batched_weights.BatchedWeights
abbrev Range := core.ops.range.Range Usize
abbrev Raw := alloc.vec.Vec (Array Std.U64 4#usize)

/-- The generated body not only succeeds: its selected lane stores exactly
the old raw value plus the product.  `hset` records the array frame update. -/
theorem push_body_step_value
    (index : Usize) (limbs : Array Std.U32 4#usize) (iter : Range)
    (self : BW) (basis : aspis_core.field.M31) (j : Usize) (iterNext : Range)
    (limb : Std.U32) (old : Array Std.U64 4#usize)
    (back : Array Std.U64 4#usize → Raw) (previous : Std.U64)
    (terms : Usize)
    (hnext : core.iter.range.IteratorRange.next core.iter.range.StepUsize iter = .ok (some j, iterNext))
    (hj : j.val < 4)
    (hlimbRead : Array.index_usize limbs j = .ok limb)
    (hlimbBound : limb.val < AspisV8R17.RawReducer.P)
    (hbasis : basis.val < AspisV8R17.RawReducer.P)
    (hvec : alloc.vec.Vec.index_mut
      (core.slice.index.SliceIndexUsizeSlice (Array Std.U64 4#usize))
      self.raw index = .ok (old, back))
    (hraw : previous.val < 2^34 + (terms.val % 4) * AspisR1BatchedAllPrefix.cap)
    (hread : Array.index_usize old j = .ok previous) :
    ∃ product sum : Std.U64, ∃ updated : Array Std.U64 4#usize,
      (limb.val * basis.val) = product.val ∧
      sum.val = previous.val + product.val ∧
      updated = old.set j sum ∧
      batched_weights.BatchedWeights.push_loop.body index limbs iter self basis =
        .ok (.cont (iterNext, { self with raw := back updated }, basis)) := by
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
  obtain ⟨product, hmul, hprodVal⟩ :=
    AspisR1.ExtractedCurrentReducerOps.mul_success limb64 basis64 hprodLt
  have hP : AspisV8R17.RawReducer.P = 2147483647 := by norm_num [AspisV8R17.RawReducer.P]
  have hcap : AspisR1BatchedAllPrefix.cap = 4611686009837453316 := by
    norm_num [AspisR1BatchedAllPrefix.cap]
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
  obtain ⟨sum, hadd, hsumVal⟩ :=
    AspisR1.ExtractedCurrentReducerOps.add_success previous product hsumLt
  have hidx : j.val < old.val.length := by simpa [old.property] using hju
  obtain ⟨updated, hupdate, hset⟩ :=
    WP.spec_imp_exists (Array.update_spec old j sum hidx)
  refine ⟨product, sum, updated, ?_, ?_, hset, ?_⟩
  · exact hprodVal'.symm
  · exact hsumVal
  · simpa [hreadLimbs, hlimb64, hbasis64, hmul, hvec, hread, hadd, hupdate] using
      AspisR1BatchedWeightsPushBodyStepV7.push_body_step
        index limbs iter self basis j iterNext x limb64 basis64 product old previous sum updated back
        hnext hreadLimbs hlimb64 hbasis64 hmul hvec hread hadd hupdate
#print axioms push_body_step_value
end AspisR1BatchedWeightsPushBodyValueStepV1
