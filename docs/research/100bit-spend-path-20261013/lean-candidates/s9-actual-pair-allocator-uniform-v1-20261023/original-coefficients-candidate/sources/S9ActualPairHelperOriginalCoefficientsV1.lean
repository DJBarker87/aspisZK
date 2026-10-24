import S9ActualPairHelperLoopToOldV1
import S9PairPublicTopResultV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairHelperOriginalCoefficientsV1
open AspisR1S9ActualPairOldCarrierScalarV1
abbrev WA := Array W 4#usize
abbrev P6W := AspisR1S9HelperP6.field.WideExact
abbrev P6Q := AspisR1S9HelperP6.field.QM31
abbrev QC := AspisR1S9ActualPairQMHelperTransportV1.Canonical
abbrev WC := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev GoodArray := AspisR1S9ActualPairScalarCallbackV1.GoodArray
abbrev CW := AspisR1S9CurrentFieldOpsV1.Canonical
abbrev HQ := AspisR1S9CandidateHighArraySemanticsV1.CanonicalP6
abbrev TraceDecode := AspisR1S9PairPublicTopResultV1.TraceDecode
abbrev ScaledBase := AspisR1S9PairPublicTopResultV1.ScaledBase
abbrev Seed := AspisR1S9PairPublicTopResultV1.Seed
abbrev cells := AspisR1S9PairPublicTopResultV1.cells
abbrev PW := AspisR1S9PairPublicTopResultV1.PairMapW
abbrev PQ := AspisR1S9PairPublicTopResultV1.PairMapQ
abbrev TW := AspisR1S9PairPublicTopResultV1.ToP6W
abbrev TQ := AspisR1S9PairPublicTopResultV1.ToP6Q

theorem composite_w (x : W) : TW (PW (toOldW x)) = toHelperW x := by
  exact (AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateW _).trans (toP6W_toOldW x)
theorem composite_q (x : Q) : TQ (PQ (toOldQ x)) = toHelperQ x := by
  exact (AspisR1S9PairCallerCandidateMapV1.candidateToP6_pairToCandidateQ _).trans (toP6Q_toOldQ x)

theorem nested_w_array (a : WA) :
    mapArray TW (mapArray PW (mapArray toOldW a)) = mapArray toHelperW a := by
  apply Subtype.ext
  change List.map TW (List.map PW (List.map toOldW a.val)) = List.map toHelperW a.val
  simp only [List.map_map]
  exact congrArg (fun (f : W → P6W) => List.map f a.val) (funext composite_w)

theorem native_w_canonical (x : W) (hx : WC x) : CW (toHelperW x) := by
  change AspisR1CurrentWide.Proof.CanonicalWide
    (AspisR1S9CurrentFieldOpsV1.toE (AspisR1S9CurrentFieldOpsV1.fromE
      (AspisR1S9ActualPairWideCanonicalV1.toCurrent x)))
  rw [AspisR1S9CurrentFieldOpsV1.to_from]
  exact hx

theorem native_w_high_canonical (x : W) (hx : WC x) :
    AspisR1S9HighTermsTraceV1.canonicalW (toHelperW x) := by
  exact native_w_canonical x hx

theorem native_q_canonical (x : Q) (hx : QC x) : HQ (toHelperQ x) := by
  exact hx

private theorem p6_reads (a : WA) (ha : GoodArray a) :
    ∀ j v, Array.index_usize (mapArray TW (mapArray PW (mapArray toOldW a))) j = .ok v → CW v := by
  intro j v hr
  have hm := congrArg (fun (b : Array P6W 4#usize) => Array.index_usize b j) (nested_w_array a)
  obtain ⟨x,hx,he⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
    toHelperW a j v (hm.symm.trans hr)
  rw [←he]
  exact native_w_canonical x (ha j x hx)

/-- The complete actual32 helper's same accepted output satisfies the existing
original S2 coefficient equations. Native canonical input-read premises are
exactly those supplied by the strict-resume/finish producer. No old helper,
body, scalar, arithmetic or output-canonicality premise remains. -/
theorem actual_helper_original_coefficients (ap0 ap1 : WA) (extra : Array Q 2#usize)
    (output : WA) (hp0 : GoodArray ap0) (hp1 : GoodArray ap1)
    (he : ∀ i q, Array.index_usize extra i = .ok q → QC q)
    (h : _root_.AspisR1S9ProductionPairCutV1.weights.factored_s2_libra_weights ap0 ap1 extra = .ok output) :
    GoodArray output ∧ ∃ q0 q1 : Q,
      Array.index_usize extra 0#usize = .ok q0 ∧
      Array.index_usize extra 1#usize = .ok q1 ∧
      (∀ j : Fin 4, CW (cells (mapArray toHelperW output) j)) ∧
      (∀ j : Fin 4,
        TraceDecode (cells (mapArray toHelperW output) j) =
          AspisR1.S2LibraFactoredIdentity.original
            (ScaledBase (mapArray toHelperW ap0)) (ScaledBase (mapArray toHelperW ap1))
            (Seed (toHelperQ q0)) (Seed (toHelperQ q1)) j) := by
  obtain ⟨hcan,hold⟩ := AspisR1S9ActualPairHelperLoopToOldV1.actual_helper_success_to_old
    ap0 ap1 extra output hp0 hp1 he h
  have hp0old := p6_reads ap0 hp0
  have hp1old : ∀ j v,
      Array.index_usize (mapArray TW (mapArray PW (mapArray toOldW ap1))) j = .ok v →
      AspisR1S9HighTermsTraceV1.canonicalW v := p6_reads ap1 hp1
  have heold : ∀ j v, Array.index_usize (mapArray PQ (mapArray toOldQ extra)) j = .ok v → HQ (TQ v) := by
    intro j v hr
    obtain ⟨oldq,holdq,hmq⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
      PQ (mapArray toOldQ extra) j v hr
    obtain ⟨q,hq,hoq⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
      toOldQ extra j oldq holdq
    rw [←hmq,←hoq,composite_q]
    exact native_q_canonical q (he j q hq)
  obtain ⟨oldq0,oldq1,hq0,hq1,hcc,hcoef⟩ :=
    AspisR1S9PairPublicTopResultV1.pair_top_success_output_canonical_and_original_coefficients
      (mapArray toOldW ap0) (mapArray toOldW ap1) (mapArray toOldQ extra) (mapArray toOldW output)
      hold hp0old hp1old heold
  obtain ⟨q0,hread0,hmap0⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
    toOldQ extra 0#usize oldq0 hq0
  obtain ⟨q1,hread1,hmap1⟩ := AspisR1S9CandidateOriginalCoefficientsBridgeV4.mapped_read_inv
    toOldQ extra 1#usize oldq1 hq1
  refine ⟨hcan,q0,q1,hread0,hread1,?_,?_⟩
  · intro j
    have hprop := congrArg (fun (aa : Array P6W 4#usize) => CW (cells aa j)) (nested_w_array output)
    exact Eq.mp hprop (hcc j)
  · intro j
    have hout := congrArg (fun (aa : Array P6W 4#usize) => TraceDecode (cells aa j)) (nested_w_array output)
    have hb0 := congrArg ScaledBase (nested_w_array ap0)
    have hb1 := congrArg ScaledBase (nested_w_array ap1)
    have hq0eq : TQ (PQ oldq0) = toHelperQ q0 :=
      (congrArg (fun (q : OQ) => TQ (PQ q)) hmap0).symm.trans (composite_q q0)
    have hq1eq : TQ (PQ oldq1) = toHelperQ q1 :=
      (congrArg (fun (q : OQ) => TQ (PQ q)) hmap1).symm.trans (composite_q q1)
    have hs0 := congrArg Seed hq0eq
    have hs1 := congrArg Seed hq1eq
    calc
      TraceDecode (cells (mapArray toHelperW output) j) =
          TraceDecode (cells (mapArray TW (mapArray PW (mapArray toOldW output))) j) := hout.symm
      _ = AspisR1.S2LibraFactoredIdentity.original
          (ScaledBase (mapArray TW (mapArray PW (mapArray toOldW ap0))))
          (ScaledBase (mapArray TW (mapArray PW (mapArray toOldW ap1))))
          (Seed (TQ (PQ oldq0))) (Seed (TQ (PQ oldq1))) j := hcoef j
      _ = AspisR1.S2LibraFactoredIdentity.original
          (ScaledBase (mapArray toHelperW ap0)) (ScaledBase (mapArray toHelperW ap1))
          (Seed (TQ (PQ oldq0))) (Seed (TQ (PQ oldq1))) j :=
        congrArg₂ (fun b0 b1 => AspisR1.S2LibraFactoredIdentity.original b0 b1
          (Seed (TQ (PQ oldq0))) (Seed (TQ (PQ oldq1))) j) hb0 hb1
      _ = _ := congrArg₂ (fun s0 s1 => AspisR1.S2LibraFactoredIdentity.original
          (ScaledBase (mapArray toHelperW ap0)) (ScaledBase (mapArray toHelperW ap1)) s0 s1 j) hs0 hs1

#print axioms composite_w
#print axioms composite_q
#print axioms nested_w_array
#print axioms native_w_canonical
#print axioms native_w_high_canonical
#print axioms native_q_canonical
#print axioms actual_helper_original_coefficients
end AspisR1S9ActualPairHelperOriginalCoefficientsV1
