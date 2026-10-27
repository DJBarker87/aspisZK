import AspisR1EbyKPushConcreteCheckedQV1
import EbyKPushDotBackend
import EbyKPushCheckedScalarCanonical
import EbyKPowerValueCanonicalToPushV5
import S5QRaw.EbyKPushDecodedProductUpdateV1
import JGi_QRawSourceForwardTotalityV1
import DotPushSourceResidues

set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow Error

namespace AspisR1S5EbyKPushTotalityV1

open AspisR1EbyKPushExplicitOpsV1

abbrev QRaw := AspisR1EbyKPushDecodedProductUpdate.QRaw
abbrev Q := AspisR1EbyKPushDotBackend.PushQ
abbrev Wide := AspisR1EbyKPushDotBackend.PushWide
abbrev Qm := AspisR1EbyKPushDotBackend.PushQm
abbrev State := AspisR1EbyKPushDotBackend.PushState
abbrev Dot := AspisR1EbyKPushDotBackend.PushDot

/-- The selected Q.raw function is outer-total on two four-word arrays when
all eight words are canonical. -/
theorem qraw_arrays_total (a b : Q)
    (ha0 : a.val[0]!.val ≤ 2^31-2) (ha1 : a.val[1]!.val ≤ 2^31-2)
    (ha2 : a.val[2]!.val ≤ 2^31-2) (ha3 : a.val[3]!.val ≤ 2^31-2)
    (hb0 : b.val[0]!.val ≤ 2^31-2) (hb1 : b.val[1]!.val ≤ 2^31-2)
    (hb2 : b.val[2]!.val ≤ 2^31-2) (hb3 : b.val[3]!.val ≤ 2^31-2) :
    ∃ raw : Array U64 4#usize, QRaw a b = .ok raw := by
  exact AspisR1S5QRawSourceTotality.qraw_total_of_canonical_limbs a b
    ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3

/-- One concrete Dot push succeeds whenever the Q.raw call is supplied by the
canonical-input totality theorem. This is the exact four-coordinate source cut. -/
theorem dot_via_raw_total
    (self : Dot) (a b : Q)
    (ha0 : a.val[0]!.val ≤ 2^31-2) (ha1 : a.val[1]!.val ≤ 2^31-2)
    (ha2 : a.val[2]!.val ≤ 2^31-2) (ha3 : a.val[3]!.val ≤ 2^31-2)
    (hb0 : b.val[0]!.val ≤ 2^31-2) (hb1 : b.val[1]!.val ≤ 2^31-2)
    (hb2 : b.val[2]!.val ≤ 2^31-2) (hb3 : b.val[3]!.val ≤ 2^31-2) :
    ∃ d : Dot, AspisR1EbyKPushDotBackend.dotViaRaw QRaw self a b = .ok d := by
  obtain ⟨raw, hraw⟩ := qraw_arrays_total a b ha0 ha1 ha2 ha3 hb0 hb1 hb2 hb3
  refine ⟨⟨AspisR1DotPushLocal.Proof.updatedSums self.sums raw⟩, ?_⟩
  unfold AspisR1EbyKPushDotBackend.dotViaRaw
  rw [AspisR1DotPushLocal.Proof.push_total_from_raw QRaw ⟨self.sums⟩ a b raw hraw]
  rfl

theorem allRun_total (xs : List Std.U32) (c : AspisR1EbyKCheckedQAllParamV1.Closure) :
    ∃ b n, AspisR1EbyKCheckedQConcreteAll.allRun
      AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureFnMut xs c = .ok (b,n) := by
  induction xs generalizing c with
  | nil => exact ⟨true,0,rfl⟩
  | cons x xs ih =>
    by_cases hp : x < AspisR1EbyKCheckedQAllParamV1.P
    · obtain ⟨b,n,hn⟩ := ih c
      refine ⟨b,n+1,?_⟩
      simp [AspisR1EbyKCheckedQConcreteAll.allRun,
        AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureFnMut,
        AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureCallMut,hp,hn]
    · refine ⟨false,1,?_⟩
      simp [AspisR1EbyKCheckedQConcreteAll.allRun,
        AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureFnMut,
        AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureCallMut,hp]

/-- If all four checked-Q limbs satisfy the source predicate, the actual
short-circuit scan returns true and therefore constructs a Q value. -/
theorem allRun_true_of_valid (xs : List Std.U32)
    (c : AspisR1EbyKCheckedQAllParamV1.Closure)
    (hvalid : ∀ x ∈ xs, x.val < 2147483647) :
    ∃ n, AspisR1EbyKCheckedQConcreteAll.allRun
      AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureFnMut xs c = .ok (true,n) := by
  induction xs generalizing c with
  | nil => exact ⟨0,rfl⟩
  | cons x xs ih =>
    have hxv := hvalid x (by simp)
    have hx : x < AspisR1EbyKCheckedQAllParamV1.P := by
      simpa [AspisR1EbyKCheckedQAllParamV1.P] using hxv
    have htail : ∀ y ∈ xs, y.val < 2147483647 := by
      intro y hy
      exact hvalid y (List.mem_cons_of_mem x hy)
    obtain ⟨n,hn⟩ := ih c htail
    refine ⟨n+1, ?_⟩
    simp [AspisR1EbyKCheckedQConcreteAll.allRun,
      AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureFnMut,
      AspisR1EbyKCheckedQAllParamV1.fromLimbsClosureCallMut,hx,hn]

theorem fromLimbsWithAll_outer_total (x : Q) :
    ∃ o, AspisR1EbyKCheckedQAllParamV1.fromLimbsWithAll
      AspisR1EbyKCheckedQConcreteAll.concreteAll x = .ok o := by
  rw [AspisR1EbyKCheckedQConcreteAll.fromLimbs_model_eq]
  obtain ⟨b,n,hn⟩ := allRun_total x.val ()
  cases b <;> simp [hn]

theorem fromLimbsWithAll_success_of_valid (x : Q)
    (hvalid : ∀ v ∈ x.val, v.val < 2147483647) :
    AspisR1EbyKCheckedQAllParamV1.fromLimbsWithAll
      AspisR1EbyKCheckedQConcreteAll.concreteAll x = .ok (some x) := by
  obtain ⟨n,hn⟩ := allRun_true_of_valid x.val () hvalid
  rw [AspisR1EbyKCheckedQConcreteAll.fromLimbs_model_eq]
  simp [hn]

theorem checked_q_success_of_valid (s : Qm)
    (hvalid : ∀ v ∈ (AspisR1EbyKPushDotBackend.scalarQ s).val,
      v.val < 2147483647) :
    ∃ q, AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
      AspisR1EbyKCheckedQConcreteAll.concreteAll s = .ok (.Ok q) := by
  let words := AspisR1EbyKPushDotBackend.scalarQ s
  have hwords : ∀ v ∈ words.val, v.val < 2147483647 := by
    simpa [words] using hvalid
  have hfrom := fromLimbsWithAll_success_of_valid words hwords
  refine ⟨words, ?_⟩
  unfold AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
  simp only [AspisR1EbyKCheckedQAllParamV1.limbsOf, bind_tc_ok]
  rw [hfrom]
  simp [AspisR1EbyKCheckedQAllParamV1.optionOkOr]

/-- The actual checked-Q path is outer-total even when its validity scan
rejects arbitrary scalar limbs; that case is a successful outer Err return. -/
theorem checked_q_outer_total (s : Qm) :
    ∃ r, AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
      AspisR1EbyKCheckedQConcreteAll.concreteAll s = .ok r := by
  unfold AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
  simp only [AspisR1EbyKCheckedQAllParamV1.limbsOf, bind_tc_ok]
  obtain ⟨o, ho⟩ := fromLimbsWithAll_outer_total
    (Array.make 4#usize [s.c0.a,s.c0.b,s.c1.a,s.c1.b])
  rw [ho]
  cases o <;> simp [AspisR1EbyKCheckedQAllParamV1.optionOkOr]

/-- Source `fromWide` returns the exact pair of four-limb arrays. -/
theorem from_wide_array_indices (v : Wide) :
    ∃ (arr : Array Q 2#usize) (x0 x1 : Q),
      AspisR1EbyKPushWideToQ.fromWide v = .ok arr ∧
      Array.index_usize arr 0#usize = .ok x0 ∧
      Array.index_usize arr 1#usize = .ok x1 ∧
      x0 = AspisR1EbyKPushDotBackend.valueLo v ∧
      x1 = AspisR1EbyKPushDotBackend.valueHi v := by
  refine ⟨AspisR1EbyKPushWideToQ.pairFromCoords
      v.c0.c0.a v.c0.c0.b v.c0.c1.a v.c0.c1.b
      v.c1.c0.a v.c1.c0.b v.c1.c1.a v.c1.c1.b,
    AspisR1EbyKPushDotBackend.valueLo v,
    AspisR1EbyKPushDotBackend.valueHi v,
    AspisR1EbyKPushWideToQ.fromWide_coordinates v, ?_, ?_, rfl, rfl⟩
  · simp [AspisR1EbyKPushWideToQ.pairFromCoords,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.index_usize, Array.make]
  · simp [AspisR1EbyKPushWideToQ.pairFromCoords,
      AspisR1EbyKPushWideToQ.qFromCoords, Array.index_usize, Array.make]

/-- Concrete successful push branch, with all potentially failing source calls
shown explicitly. The checked-Q rejection case is handled separately by the
caller and does not assume scalar canonicality. -/
theorem push_ops_continue_success
    (self : State) (value : Wide) (scalar : Qm)
    (arr : Array Q 2#usize) (x0 x1 q : Q) (d0 d1 : Dot) (i : Usize)
    (hcount : self.count < maxTerms)
    (hfrom : AspisR1EbyKPushWideToQ.fromWide value = .ok arr)
    (hx0 : Array.index_usize arr 0#usize = .ok x0)
    (hx1 : Array.index_usize arr 1#usize = .ok x1)
    (hq : AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
      AspisR1EbyKCheckedQConcreteAll.concreteAll scalar = .ok (.Ok q))
    (hd0 : AspisR1EbyKPushDotBackend.dotViaRaw QRaw self.c0 x0 q = .ok d0)
    (hd1 : AspisR1EbyKPushDotBackend.dotViaRaw QRaw self.c1 x1 q = .ok d1)
    (hadd : UScalar.add self.count 1#usize = .ok i) :
    AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
      AspisR1EbyKCheckedQConcreteAll.concreteAll
      (AspisR1EbyKPushDotBackend.dotViaRaw QRaw) self value scalar =
        .ok (.Ok (), { c0 := d0, c1 := d1, count := i }) := by
  unfold AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
    AspisR1EbyKPushSourceConversionV1.pushWithSourceCheckedAdd
    AspisR1EbyKPushSourceConversionV1.pushWithSourceConversion
    AspisR1EbyKPushExplicitOpsV1.pushWithOps
  simp only [if_neg (not_le_of_gt hcount), hfrom, bind_tc_ok, hx0, hx1, hq,
    core.result.Result.Insts.CoreOpsTry.branch, hd0, hd1, hadd, bind_tc_ok]

/-- Successful scalar rejection is represented by an ordinary inner Err while
retaining the original state; it is not an outer failure/divergence. -/
theorem push_ops_checked_q_reject
    (self : State) (value : Wide) (scalar : Qm)
    (arr : Array Q 2#usize) (x0 x1 : Q) (e : Unit)
    (hcount : self.count < maxTerms)
    (hfrom : AspisR1EbyKPushWideToQ.fromWide value = .ok arr)
    (hx0 : Array.index_usize arr 0#usize = .ok x0)
    (hx1 : Array.index_usize arr 1#usize = .ok x1)
    (hq : AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
      AspisR1EbyKCheckedQConcreteAll.concreteAll scalar = .ok (.Err e)) :
    AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
      AspisR1EbyKCheckedQConcreteAll.concreteAll
      (AspisR1EbyKPushDotBackend.dotViaRaw QRaw) self value scalar =
        .ok (.Err (), self) := by
  unfold AspisR1EbyKPushConcreteCheckedQV1.pushWithConcreteCheckedQ
    AspisR1EbyKPushSourceConversionV1.pushWithSourceCheckedAdd
    AspisR1EbyKPushSourceConversionV1.pushWithSourceConversion
    AspisR1EbyKPushExplicitOpsV1.pushWithOps
  simp only [if_neg (not_le_of_gt hcount), hfrom, bind_tc_ok, hx0, hx1, hq,
    core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok,
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual]

private theorem checked_count_add_total (n : Usize) (hn : n < maxTerms) :
    ∃ i, UScalar.add n 1#usize = .ok i := by
  unfold AspisR1EbyKPushExplicitOpsV1.maxTerms at hn
  have hnval : n.val < 4096 := by
    simpa using hn
  have hroom : n.val + 1 ≤ Std.Usize.max := by
    have hmax : 4096 ≤ Std.Usize.max := by scalar_tac
    omega
  have haddSpec : UScalar.add n 1#usize ⦃z => z.val = n.val + 1⦄ := by
    apply UScalar.add_spec
    have hsum : n.val + (1#usize).val ≤ Std.Usize.max := by simpa using hroom
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨i, hadd, _⟩ := WP.spec_imp_exists haddSpec
  exact ⟨i,hadd⟩

/-- The full selected source-model EbyK push has an outer Result value on every
canonical value and every pre-call count admitted by the source guard. The
inner checked-Q rejection remains a normal `.Err` result, so scalar inputs need
not be canonical for outer totality. -/
theorem push_outer_total
    (self : State) (value : Wide) (scalar : Qm)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical value)
    (hcount : self.count < maxTerms) :
    ∃ answer,
      AspisR1EbyKPushDotBackend.pushWithDotBackend QRaw self value scalar =
        .ok answer := by
  obtain ⟨checked, hchecked⟩ := checked_q_outer_total scalar
  obtain ⟨arr,x0,x1,hfrom,hx0,hx1,hx0v,hx1v⟩ := from_wide_array_indices value
  cases checked with
  | Err e =>
    refine ⟨(.Err (),self), ?_⟩
    simpa [AspisR1EbyKPushDotBackend.pushWithDotBackend] using
      push_ops_checked_q_reject self value scalar arr x0 x1 e hcount hfrom hx0 hx1 hchecked
  | Ok q =>
    have hq : AspisR1EbyKCheckedQAllParamV1.checkedQWithAll
      AspisR1EbyKCheckedQConcreteAll.concreteAll scalar = .ok (.Ok q) := hchecked
    have hqcanon := AspisR1EbyKCheckedQConcreteAll.checkedQ_success_canonical scalar q hq
    have hb := AspisR1EbyKPowerValueCanonicalToPush.canonical_push_limb_bounds value hcanonical
    have hq0 : q.val[0]!.val ≤ 2^31-2 := by
      have hm : scalar.c0.a ∈ q.val := by rw [hqcanon.1]; simp [Array.make]
      have hs := hqcanon.2 scalar.c0.a hm
      have hv : q.val[0]!.val = scalar.c0.a.val := by
        rw [hqcanon.1]
        simp [Array.make]
      rw [hv]
      omega
    have hq1 : q.val[1]!.val ≤ 2^31-2 := by
      have hm : scalar.c0.b ∈ q.val := by rw [hqcanon.1]; simp [Array.make]
      have hs := hqcanon.2 scalar.c0.b hm
      have hv : q.val[1]!.val = scalar.c0.b.val := by
        rw [hqcanon.1]
        simp [Array.make]
      rw [hv]
      omega
    have hq2 : q.val[2]!.val ≤ 2^31-2 := by
      have hm : scalar.c1.a ∈ q.val := by rw [hqcanon.1]; simp [Array.make]
      have hs := hqcanon.2 scalar.c1.a hm
      have hv : q.val[2]!.val = scalar.c1.a.val := by
        rw [hqcanon.1]
        simp [Array.make]
      rw [hv]
      omega
    have hq3 : q.val[3]!.val ≤ 2^31-2 := by
      have hm : scalar.c1.b ∈ q.val := by rw [hqcanon.1]; simp [Array.make]
      have hs := hqcanon.2 scalar.c1.b hm
      have hv : q.val[3]!.val = scalar.c1.b.val := by
        rw [hqcanon.1]
        simp [Array.make]
      rw [hv]
      omega
    have hdot0 := dot_via_raw_total self.c0 x0 q
      (by rw [hx0v]; simpa [AspisR1EbyKPushDotBackend.valueLo,
        AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.1)
      (by rw [hx0v]; simpa [AspisR1EbyKPushDotBackend.valueLo,
        AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.1)
      (by rw [hx0v]; simpa [AspisR1EbyKPushDotBackend.valueLo,
        AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.1)
      (by rw [hx0v]; simpa [AspisR1EbyKPushDotBackend.valueLo,
        AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.1)
      hq0 hq1 hq2 hq3
    have hdot1 := dot_via_raw_total self.c1 x1 q
      (by rw [hx1v]; simpa [AspisR1EbyKPushDotBackend.valueHi,
        AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.2.1)
      (by rw [hx1v]; simpa [AspisR1EbyKPushDotBackend.valueHi,
        AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.2.2.1)
      (by rw [hx1v]; simpa [AspisR1EbyKPushDotBackend.valueHi,
        AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.2.2.2.1)
      (by rw [hx1v]; simpa [AspisR1EbyKPushDotBackend.valueHi,
        AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.2.2.2.2)
      hq0 hq1 hq2 hq3
    obtain ⟨d0,hd0⟩ := hdot0
    obtain ⟨d1,hd1⟩ := hdot1
    obtain ⟨i,hadd⟩ := checked_count_add_total self.count hcount
    refine ⟨(.Ok (),{c0:=d0,c1:=d1,count:=i}),?_⟩
    apply push_ops_continue_success self value scalar arr x0 x1 q d0 d1 i
      hcount hfrom hx0 hx1 hq hd0 hd1 hadd

/-- When the scalar's four source limbs pass the actual checked-Q predicate,
the selected EbyK push succeeds (with both Q.raw-backed Dot updates and the
checked numeric count increment). -/
theorem push_success_of_valid_scalar
    (self : State) (value : Wide) (scalar : Qm)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical value)
    (hcount : self.count < maxTerms)
    (hscalar : ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ scalar).val,
      x.val < 2147483647) :
    ∃ out, AspisR1EbyKPushDotBackend.pushWithDotBackend QRaw self value scalar =
      .ok (.Ok (),out) := by
  have hvalid : ∀ x ∈
      (AspisR1EbyKPushDotBackend.scalarQ scalar).val,
      x.val < 2147483647 := by
    exact hscalar
  obtain ⟨q,hq⟩ := checked_q_success_of_valid scalar hvalid
  have hqcanon := AspisR1EbyKCheckedQConcreteAll.checkedQ_success_canonical
    scalar q hq
  obtain ⟨arr,x0,x1,hfrom,hx0,hx1,hx0v,hx1v⟩ := from_wide_array_indices value
  have hb := AspisR1EbyKPowerValueCanonicalToPush.canonical_push_limb_bounds
    value hcanonical
  have hq0 : q.val[0]!.val ≤ 2^31-2 := by
    have hv : q.val[0]!.val = scalar.c0.a.val := by
      rw [hqcanon.1]
      simp [Array.make]
    have hm : scalar.c0.a ∈ (AspisR1EbyKPushDotBackend.scalarQ scalar).val := by
      simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]
    rw [hv]
    have hs := hscalar scalar.c0.a hm
    omega
  have hq1 : q.val[1]!.val ≤ 2^31-2 := by
    have hv : q.val[1]!.val = scalar.c0.b.val := by
      rw [hqcanon.1]
      simp [Array.make]
    have hm : scalar.c0.b ∈ (AspisR1EbyKPushDotBackend.scalarQ scalar).val := by
      simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]
    rw [hv]
    have hs := hscalar scalar.c0.b hm
    omega
  have hq2 : q.val[2]!.val ≤ 2^31-2 := by
    have hv : q.val[2]!.val = scalar.c1.a.val := by
      rw [hqcanon.1]
      simp [Array.make]
    have hm : scalar.c1.a ∈ (AspisR1EbyKPushDotBackend.scalarQ scalar).val := by
      simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]
    rw [hv]
    have hs := hscalar scalar.c1.a hm
    omega
  have hq3 : q.val[3]!.val ≤ 2^31-2 := by
    have hv : q.val[3]!.val = scalar.c1.b.val := by
      rw [hqcanon.1]
      simp [Array.make]
    have hm : scalar.c1.b ∈ (AspisR1EbyKPushDotBackend.scalarQ scalar).val := by
      simp [AspisR1EbyKPushDotBackend.scalarQ, Array.make]
    rw [hv]
    have hs := hscalar scalar.c1.b hm
    omega
  have hdot0 := dot_via_raw_total self.c0 x0 q
    (by rw [hx0v]; simpa [AspisR1EbyKPushDotBackend.valueLo,
      AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.1)
    (by rw [hx0v]; simpa [AspisR1EbyKPushDotBackend.valueLo,
      AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.1)
    (by rw [hx0v]; simpa [AspisR1EbyKPushDotBackend.valueLo,
      AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.1)
    (by rw [hx0v]; simpa [AspisR1EbyKPushDotBackend.valueLo,
      AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.1)
    hq0 hq1 hq2 hq3
  have hdot1 := dot_via_raw_total self.c1 x1 q
    (by rw [hx1v]; simpa [AspisR1EbyKPushDotBackend.valueHi,
      AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.2.1)
    (by rw [hx1v]; simpa [AspisR1EbyKPushDotBackend.valueHi,
      AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.2.2.1)
    (by rw [hx1v]; simpa [AspisR1EbyKPushDotBackend.valueHi,
      AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.2.2.2.1)
    (by rw [hx1v]; simpa [AspisR1EbyKPushDotBackend.valueHi,
      AspisR1EbyKPushWideToQ.qFromCoords,Array.make] using hb.2.2.2.2.2.2.2)
    hq0 hq1 hq2 hq3
  obtain ⟨d0,hd0⟩ := hdot0
  obtain ⟨d1,hd1⟩ := hdot1
  obtain ⟨i,hadd⟩ := checked_count_add_total self.count hcount
  have hpush := push_ops_continue_success self value scalar arr x0 x1 q d0 d1 i
    hcount hfrom hx0 hx1 hq hd0 hd1 hadd
  refine ⟨{c0:=d0,c1:=d1,count:=i}, ?_⟩
  simpa [AspisR1EbyKPushDotBackend.pushWithDotBackend] using hpush

/-- The successful valid-scalar branch of the concrete emitted push carries
the retained QRaw arithmetic law for both Dot accumulators.  The two
`2^46` accumulator bounds remain explicit state invariants. -/
theorem push_success_product_update_of_valid_scalar
    (self : State) (value : Wide) (scalar : Qm)
    (hcanonical : AspisR1EbyKPowerValueCanonicalToPush.pushCanonical value)
    (hcount : self.count < maxTerms)
    (hscalar : ∀ x ∈ (AspisR1EbyKPushDotBackend.scalarQ scalar).val,
      x.val < 2147483647)
    (hacc0 : ∀ x ∈ self.c0.sums.val, x.val < 2^46)
    (hacc1 : ∀ x ∈ self.c1.sums.val, x.val < 2^46) :
    ∃ out,
      AspisR1EbyKPushDotBackend.pushWithDotBackend QRaw self value scalar =
        .ok (.Ok (),out) ∧
      AspisR1EbyKPushDecodedProductUpdate.castSums out.c0.sums =
        AspisR1EbyKPushDecodedProductUpdate.tupleAdd
          (AspisR1EbyKPushDecodedProductUpdate.castSums self.c0.sums)
          (AspisR1.R22RawQmProductResidues.qmulCoefficients
            ((value.c0.c0.a.val,value.c0.c0.b.val),
             (value.c0.c1.a.val,value.c0.c1.b.val))
            ((scalar.c0.a.val,scalar.c0.b.val),
             (scalar.c1.a.val,scalar.c1.b.val))) ∧
      AspisR1EbyKPushDecodedProductUpdate.castSums out.c1.sums =
        AspisR1EbyKPushDecodedProductUpdate.tupleAdd
          (AspisR1EbyKPushDecodedProductUpdate.castSums self.c1.sums)
          (AspisR1.R22RawQmProductResidues.qmulCoefficients
            ((value.c1.c0.a.val,value.c1.c0.b.val),
             (value.c1.c1.a.val,value.c1.c1.b.val))
            ((scalar.c0.a.val,scalar.c0.b.val),
             (scalar.c1.a.val,scalar.c1.b.val))) := by
  obtain ⟨out,hrun⟩ := push_success_of_valid_scalar self value scalar
    hcanonical hcount hscalar
  have hupdate :=
    AspisR1EbyKPushDecodedProductUpdate.successful_push_decoded_product_update
      self value scalar out hcanonical hacc0 hacc1 hrun
  exact ⟨out,hrun,hupdate.1,hupdate.2⟩

#print axioms qraw_arrays_total
#print axioms dot_via_raw_total
#print axioms allRun_total
#print axioms fromLimbsWithAll_outer_total
#print axioms checked_q_outer_total
#print axioms from_wide_array_indices
#print axioms checked_count_add_total
#print axioms push_outer_total
#print axioms allRun_true_of_valid
#print axioms fromLimbsWithAll_success_of_valid
#print axioms checked_q_success_of_valid
#print axioms push_success_of_valid_scalar
#print axioms push_success_product_update_of_valid_scalar
#print axioms push_ops_continue_success
#print axioms push_ops_checked_q_reject
end AspisR1S5EbyKPushTotalityV1
