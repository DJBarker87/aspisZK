import S9ActualPairSharedFinalTraceV1
import S9RegularPartsCanonicalV1
import S9SharedHighScalarAssemblyV1
import S9ActualLow16LoopMeaningV1
import S9S2InactiveCanonicalV1
import S9FactoredActiveCanonicalV1
import S9CanonicalPartsUpdateV1
import S9ActualPairPowersProducerV1
import S9PairLoop1SelfComponentV3
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ActualSharedParentPartsCanonicalV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualProcessKindTensorReachedV1
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev Good := AspisR1S9ActualFinalSumV1.Good
variable [allocation : AspisR1S9AllocationInterfaceV1.Allocation]

private theorem assembly_good (partials : Array W 4#usize) (self : weights.Weights)
    (ap0 ap1 : Powers) (parts out : Parts)
    (h : AspisR1S9SharedHighScalarAssemblyV1.Assembly partials self ap0 ap1 parts out) : Good out := by
  rcases h with ⟨row0,row2,high0,high2,f00,f01,f20,f21,dot0,dot2,s00,s01,s20,s21,
    scale0,scale2,product0,product2,h⟩
  repeat' first | exact h.1 | rcases h with ⟨_,h⟩

/-- SAME accepted shared two-fold native Pair supplies its final parts and
kappa powers. Every intervening canonicality obligation is discharged by the
same traced child executions. Actual receiver/alpha canonical inputs and the
exact source span remain explicit for the concrete caller to supply. -/
theorem actual_pair_shared_final_parts_canonical
    (self : weights.Weights) (alpha : Slice W) (f : Slice U8) (kappa out : W)
    (hs2 : self.variant=transport.Variant.S2)
    (hfactors : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical self)
    (hextra : ∀ i q,Array.index_usize self.extra i=.ok q →
      AspisR1S9ActualPairQMHelperTransportV1.Canonical q)
    (halpha : ∀ i x,Slice.index_usize alpha i=.ok x → Can x)
    (hfold : Slice.len alpha=2#usize)
    (hspan : Slice.len f=Usize.wrapping_mul 64#usize 32#usize)
    (hguard : weights.shared_two_point_guard self 2#usize=.ok true)
    (hpair : weights.Weights.pair self alpha f kappa=.ok (.Ok out)) :
    ∃ (parts : Parts) (k : Array W 7#usize),
      Good parts ∧ weights.powers 7#usize kappa=.ok k ∧
      weights.Weights.pair_loop9 {start:=0#usize,«end»:=7#usize} parts k
        aspis_core.field.wide_exact.WideExact.ZERO=.ok out := by
  obtain ⟨n,a0,a1,ap0,ap1,scratch,scratchOut,partsRegular,partsShared,
    selfCommon,common,partials,low,inactive,partsInactive,partsFinal,useFactored,libra,k,
    hn,hn64,ha0,hap0,ha1,hap1,hreserved,hregular,hcommon,hpartials,hhigh,
    hlow,hinactive,hpartsInactive,huse,hlibra,hactive,hk,hsum⟩ :=
    AspisR1S9ActualPairSharedFinalTraceV1.actual_pair_success_shared_final_trace
      self alpha f kappa out hfold hguard hpair
  have hp0 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical
    a0 ap0 (halpha 0#usize a0 ha0) hap0
  have hp1 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical
    a1 ap1 (halpha 1#usize a1 ha1) hap1
  have hsame := AspisR1S9PairLoop1SelfComponentV3.pair_loop1_first_component
    {start:=0#usize,«end»:=16#usize} self selfCommon
    (Array.repeat 16#usize aspis_core.field.QM31.ZERO) common hcommon
  subst selfCommon
  have creg := AspisR1S9RegularPartsCanonicalV1.regular_from_zero_success_good
    self true alpha f n ap0 ap1 scratch scratchOut partsRegular hs2 hp0 hp1 hregular
  have ashared := AspisR1S9SharedHighScalarAssemblyV1.shared_high_success_value_assembly
    partials self ap0 ap1 partsRegular partsShared hfactors hp0 hp1 creg hhigh
  have cshared := assembly_good partials self ap0 ap1 partsRegular partsShared ashared
  have clow := (AspisR1S9ActualLow16LoopMeaningV1.actual_shared_low_loop_success
    ap0 ap1 {start:=0#usize,«end»:=16#usize}
    (Array.repeat 16#usize aspis_core.field.wide_exact.WideExact.ZERO) low
    hp0 hp1 rfl rfl hlow).2
  have cinactive := AspisR1S9S2InactiveCanonicalV1.s2_exact_span_dispatch_success_canonical
    self f low inactive hs2 hspan clow hinactive
  have cpartsInactive := AspisR1S9CanonicalPartsUpdateV1.update_preserves_good
    partsShared partsInactive 0#usize inactive (by decide) cshared cinactive hpartsInactive
  have heq : transport.Variant.Insts.CoreCmpPartialEqVariant.eq self.variant
      transport.Variant.S2=.ok true := by
    rw [hs2]
    simp [transport.Variant.Insts.CoreCmpPartialEqVariant.eq,transport.Variant.read_discriminant]
  have htrue : useFactored=true := Result.ok.inj (huse.symm.trans heq)
  subst useFactored
  simp only [↓reduceIte] at hlibra
  have cfinal := AspisR1S9FactoredActiveCanonicalV1.factored_active_success_canonical
    ap0 ap1 self.extra libra f partsInactive partsFinal hp0 hp1 hextra
    cpartsInactive hlibra hactive
  exact ⟨partsFinal,k,cfinal,hk,hsum⟩

#print axioms actual_pair_shared_final_parts_canonical
end AspisR1S9ActualSharedParentPartsCanonicalV1
