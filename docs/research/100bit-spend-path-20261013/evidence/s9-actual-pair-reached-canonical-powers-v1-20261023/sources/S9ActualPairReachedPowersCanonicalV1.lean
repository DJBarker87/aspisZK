import S9ActualPairReachedFactoredHelperV1
import S9ActualPairPowersProducerV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualPairReachedPowersCanonicalV1
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical

def ArrayCanonical (a : Array W 4#usize) : Prop :=
  ∀ (i : Usize) (v : W), Array.index_usize a i = .ok v → Can v

/-- An accepted actual S2/two-fold Pair execution itself supplies the two
successful powers producers and the same factored-helper call. Only the
canonicality of reads of the actual alpha input is retained. No independent
powers success, powers-output contract, or helper success is assumed. -/
theorem actual_pair_success_reaches_canonical_powers_helper
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hs2 : self.variant = transport.Variant.S2) (hfold : Slice.len alpha = 2#usize)
    (halpha : ∀ (i : Usize) (v : W), Slice.index_usize alpha i = .ok v → Can v)
    (h : weights.Weights.pair self alpha f kappa = .ok (.Ok out)) :
    ∃ (a0 a1 : W) (ap0 ap1 libra : Array W 4#usize),
      Slice.index_usize alpha 0#usize = .ok a0 ∧
      weights.powers 4#usize a0 = .ok ap0 ∧
      Slice.index_usize alpha 1#usize = .ok a1 ∧
      weights.powers 4#usize a1 = .ok ap1 ∧
      ArrayCanonical ap0 ∧ ArrayCanonical ap1 ∧
      weights.factored_s2_libra_weights ap0 ap1 self.extra = .ok libra := by
  obtain ⟨a0,a1,ap0,ap1,libra,ha0,hap0,ha1,hap1,hhelper⟩ :=
    AspisR1S9ActualPairReachedFactoredHelperV1.actual_pair_success_reaches_factored_helper
      self alpha f kappa out hs2 hfold h
  refine ⟨a0,a1,ap0,ap1,libra,ha0,hap0,ha1,hap1,?_,?_,hhelper⟩
  · exact AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical
      a0 ap0 (halpha 0#usize a0 ha0) hap0
  · exact AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical
      a1 ap1 (halpha 1#usize a1 ha1) hap1

#print axioms actual_pair_success_reaches_canonical_powers_helper
end AspisR1S9ActualPairReachedPowersCanonicalV1
