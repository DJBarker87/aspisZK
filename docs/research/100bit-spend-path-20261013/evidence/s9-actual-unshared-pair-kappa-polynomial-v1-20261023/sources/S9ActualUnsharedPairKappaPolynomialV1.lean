import S9ActualUnsharedParentPartsCanonicalV1
import S9ActualKappaFinalSumV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualUnsharedPairKappaPolynomialV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
/-- One accepted unshared two-fold Pair returns the kappa polynomial of its
own canonical final parts. Source caller guards remain explicit; no child
execution, powers array, final parts, or canonical final output is assumed.
The parts-to-spend-relation interpretation is a separate theorem. -/
theorem actual_unshared_pair_returns_kappa_polynomial
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hs2 : self.variant=transport.Variant.S2)
    (hextra : ∀ i q,Array.index_usize self.extra i=.ok q →
      AspisR1S9ActualPairQMHelperTransportV1.Canonical q)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hfold : Slice.len alpha=2#usize)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (hguard : weights.shared_two_point_guard self 2#usize=.ok false)
    (hpair : weights.Weights.pair self alpha f kappa=.ok (.Ok out))
    (hkappa : Can kappa) :
    ∃ parts : Parts, AspisR1S9ActualFinalSumV1.Good parts ∧ Can out ∧
      AspisR1S9NativeWideDecodedArithmeticV1.decode out=
        AspisR1S9ActualKappaFinalSumV1.kappaPolynomial parts kappa := by
  obtain ⟨parts,k,hparts,hk,hs⟩ :=
    AspisR1S9ActualUnsharedParentPartsCanonicalV1.actual_pair_unshared_final_parts_canonical
      self alpha f kappa out hs2 hextra halpha hfold hspan hguard hpair
  obtain ⟨hout,hvalue⟩ :=
    AspisR1S9ActualKappaFinalSumV1.actual_final_sum_is_kappa_polynomial
      parts k kappa out hkappa hparts hk hs
  exact ⟨parts,hparts,hout,hvalue⟩
#print axioms actual_unshared_pair_returns_kappa_polynomial
end AspisR1S9ActualUnsharedPairKappaPolynomialV1
