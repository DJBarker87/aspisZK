import S3S9ConcreteWideMulQM31ScalarProductV1
import S9WideMulM31ReuseRootV2
import S4FromFnP6GeneratedInterface
import S4FromFnP6FourTraceV1

open Aeneas Aeneas.Std Result
set_option autoImplicit false

namespace AspisR1S9HighTermsConcreteV1

open AspisR1S9HelperP6
open AspisR1FromFnP6Generated

local instance highTermsOps : AspisR1S9HelperP6.FieldOps :=
  AspisR1S9ConcreteFieldOpsV1.concreteFieldOps

abbrev W := AspisR1S9HelperP6.field.WideExact
abbrev Q := AspisR1S9HelperP6.field.QM31
abbrev Callback := weights.factored_s2_libra_weights.closure
abbrev CallbackFn :=
  weights.factored_s2_libra_weights.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact

private abbrev canonicalW (x : W) : Prop :=
  AspisR1CurrentWide.Proof.CanonicalWide (AspisR1S9GeneratedWideMulQM31V2.toWide x)
private abbrev canonicalQ (x : Q) : Prop :=
  AspisR1CurrentWide.Proof.CanonicalQM (AspisR1S9GeneratedWideMulQM31V2.toQM x)
private abbrev decW (x : W) : AspisWideTower.WideExact :=
  AspisR1CurrentWide.Proof.decodeWide (AspisR1S9GeneratedWideMulQM31V2.toWide x)
private abbrev decQ (x : Q) : AspisR1S9HelperP6PowerSemanticsV1.ExactQM :=
  AspisR1CurrentWide.Proof.decodeQM (AspisR1S9GeneratedWideMulQM31V2.toQM x)

private theorem perm_entry_bound (i : Fin 4) :
    UScalar.val (weights.PERM.val[i.val]'(by
      have hlen := Array.length_eq weights.PERM
      have h4 : (4#usize).val = 4 := by decide
      rw [hlen, h4]
      exact i.isLt)) < 4 := by
  fin_cases i <;> norm_num [weights.PERM, Array.make]

theorem toE_eq_generated_toWide (x : W) :
    AspisR1S9CurrentFieldOpsV1.toE x = AspisR1S9GeneratedWideMulQM31V2.toWide x := by
  cases x <;> rfl

private theorem current_decode_eq_decW (x : W) :
    AspisR1S9CurrentFieldOpsV1.decode x = decW x := by
  change AspisR1CurrentWide.Proof.decodeWide (AspisR1S9CurrentFieldOpsV1.toE x) = _
  rw [toE_eq_generated_toWide]

theorem one_call (ap1 : Array W (4#usize))
    (high : Array Q (4#usize)) (i : Usize) (hi : i.val < 4)
    (hap1 : ∀ (j : Usize) (x : W), Array.index_usize ap1 j = .ok x → canonicalW x)
    (hhigh : ∀ (j : Usize) (q : Q), Array.index_usize high j = .ok q → canonicalQ q) :
    ∃ term perm x q,
      Array.index_usize weights.PERM i = .ok perm ∧
      Array.index_usize ap1 perm = .ok x ∧
      Array.index_usize high i = .ok q ∧
      CallbackFn.call_mut (ap1, high) i = .ok (term, (ap1, high)) ∧
      canonicalW term ∧
      decW term =
        (decW x * algebraMap
          AspisR1S9HelperP6PowerSemanticsV1.ExactQM AspisWideTower.WideExact (decQ q)) *
          AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER := by
  have hpermBound : i.val < weights.PERM.val.length := by
    have hlen := Array.length_eq weights.PERM
    have h4 : (4#usize).val = 4 := by decide
    omega
  obtain ⟨perm, hperm, hpermValue⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec weights.PERM i hpermBound)
  have h4 : (4#usize).val = 4 := by decide
  have hpermVal : UScalar.val perm < 4 := by
    rw [hpermValue]
    exact perm_entry_bound ⟨i.val, hi⟩
  have hap1Bound : UScalar.val perm < ap1.val.length := by
    have hlen := Array.length_eq ap1
    omega
  obtain ⟨x, hreadX, _hxval⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec ap1 perm hap1Bound)
  have hhighBound : i.val < high.val.length := by
    have hlen := Array.length_eq high
    omega
  obtain ⟨q, hreadQ, _hqval⟩ :=
    WP.spec_imp_exists (Array.index_usize_spec high i hhighBound)
  have hx := hap1 perm x hreadX
  have hq := hhigh i q hreadQ
  obtain ⟨mid, hmid, hmidCan, hmidDecode⟩ :=
    AspisR1S9ConcreteWideMulQM31ScalarProductV1.concrete_wideMulQM31_total_scalar_product
      x q hx hq
  obtain ⟨term, hterm, htermCan, htermDecode⟩ :=
    AspisR1.S9WideMulM31ReuseRootV2.concrete_wideMulM31_total_exact
      mid weights.QUARTER hmidCan
  refine ⟨term, perm, x, q, hperm, hreadX, hreadQ, ?_, htermCan, ?_⟩
  · change (do
      let permutation ← Array.index_usize weights.PERM i
      let xv ← Array.index_usize ap1 permutation
      let qv ← Array.index_usize high i
      let product ← @FieldOps.wideMulQM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps xv qv
      let value ← @FieldOps.wideMulM31
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps product weights.QUARTER
      .ok (value, (ap1, high))) = .ok (term, (ap1, high))
    simp only [hperm, hreadX, hreadQ, hmid, hterm, bind_tc_ok]
  · have htermDecode' : decW term = decW mid *
        AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER := by
      calc
        decW term = AspisR1S9CurrentFieldOpsV1.decode term := (current_decode_eq_decW term).symm
        _ = AspisR1S9CurrentFieldOpsV1.decode mid *
            AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER := htermDecode
        _ = decW mid * AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER := by
          rw [current_decode_eq_decW]
    have hmidDecode' : decW mid = decW x * algebraMap
        AspisR1S9HelperP6PowerSemanticsV1.ExactQM AspisWideTower.WideExact (decQ q) := by
      simpa [decW, decQ] using hmidDecode
    rw [htermDecode', hmidDecode']


/-- Pack one exact concrete callback success together with its selected reads
and arithmetic meaning. Defined in the same owner as `one_call`, so all field
and callback aliases are definitionally identical. -/
structure HighTermCall (ap1 : Array W (4#usize)) (high : Array Q (4#usize))
    (i : Usize) where
  term : W
  perm : Usize
  x : W
  q : Q
  perm_read : Array.index_usize weights.PERM i = .ok perm
  ap1_read : Array.index_usize ap1 perm = .ok x
  high_read : Array.index_usize high i = .ok q
  callback_success : CallbackFn.call_mut (ap1,high) i = .ok (term,(ap1,high))
  term_canonical : canonicalW term
  term_decode : decW term = (decW x * algebraMap
      AspisR1S9HelperP6PowerSemanticsV1.ExactQM AspisWideTower.WideExact (decQ q)) *
      AspisR1CurrentWide.Proof.wideScalarEmbedding weights.QUARTER

theorem one_call_record (ap1 : Array W (4#usize)) (high : Array Q (4#usize))
    (i : Usize) (hi : i.val < 4)
    (hap1 : ∀ (j : Usize) (x : W), Array.index_usize ap1 j = .ok x → canonicalW x)
    (hhigh : ∀ (j : Usize) (q : Q), Array.index_usize high j = .ok q → canonicalQ q) :
    Nonempty (HighTermCall ap1 high i) := by
  obtain ⟨term,perm,x,q,hperm,hx,hq,hcall,hcan,hdecode⟩ :=
    one_call ap1 high i hi hap1 hhigh
  exact ⟨⟨term,perm,x,q,hperm,hx,hq,hcall,hcan,hdecode⟩⟩

#print axioms one_call
#print axioms one_call_record


end AspisR1S9HighTermsConcreteV1
