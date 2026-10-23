import S9PairCallerStepOperationBridgeV1
import S9WideAddConcreteMapV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1S9PairAddChainCanonicalV1

abbrev W := AspisR1S9PairCallerStepV1.field.WideExact
abbrev PairCM := AspisR1S9PairCallerStepV1.field.CM31
abbrev PairQM := AspisR1S9PairCallerStepV1.field.QM31
abbrev SourceCM := AspisR1S9WideAddSourceBodyV1.field.CM31
abbrev SourceQM := AspisR1S9WideAddSourceBodyV1.field.QM31
abbrev SourceW := AspisR1S9WideAddSourceBodyV1.field.wide_exact.WideExact
abbrev Canonical := AspisR1S9CurrentFieldOpsV1.Canonical

private def pairToSourceCM (x : PairCM) : SourceCM := ⟨x.a,x.b⟩
private def pairToSourceQM (x : PairQM) : SourceQM :=
  ⟨pairToSourceCM x.c0,pairToSourceCM x.c1⟩
private def pairToSourceW (x : W) : SourceW :=
  ⟨pairToSourceQM x.c0,pairToSourceQM x.c1⟩

private theorem source_to_helper_pair (x : W) :
    AspisR1S9WideAddConcreteMapV1.toHelperWide (pairToSourceW x) =
      AspisR1S9PairCallerStepV1.toP6W x := by
  cases x <;> rfl

/-- Canonicality of a successful Pair addition is obtained from the exact
transparent source addition and its checked-slot simulation. We do not equate
wrapping source arithmetic with checked current arithmetic without canonical
inputs. -/
theorem pair_add_success_canonical (x y z : W)
    (hx : Canonical (AspisR1S9PairCallerStepV1.toP6W x))
    (hy : Canonical (AspisR1S9PairCallerStepV1.toP6W y))
    (hxy : AspisR1S9PairCallerStepV1.field.WideExact.add x y = .ok z) :
    Canonical (AspisR1S9PairCallerStepV1.toP6W z) := by
  let sx := pairToSourceW x
  let sy := pairToSourceW y
  have hsourceHx : Canonical
      (AspisR1S9WideAddTowerSourceMapV1.toHelperWide sx) := by
    change Canonical
      (AspisR1S9WideAddConcreteMapV1.toHelperWide (pairToSourceW x))
    rw [source_to_helper_pair x]
    exact hx
  have hsourceHy : Canonical
      (AspisR1S9WideAddTowerSourceMapV1.toHelperWide sy) := by
    change Canonical
      (AspisR1S9WideAddConcreteMapV1.toHelperWide (pairToSourceW y))
    rw [source_to_helper_pair y]
    exact hy
  have hsx : AspisR1S9WideAddConcreteMapV1.SourceCanonical sx :=
    (AspisR1S9WideAddTowerSourceMapV1.source_wide_canonical_iff_helper sx).mpr hsourceHx
  have hsy : AspisR1S9WideAddConcreteMapV1.SourceCanonical sy :=
    (AspisR1S9WideAddTowerSourceMapV1.source_wide_canonical_iff_helper sy).mpr hsourceHy
  obtain ⟨sz, hsource, hslot, hsourceOutCan⟩ :=
    AspisR1S9WideAddConcreteMapV1.source_wide_add_maps_to_concrete sx sy hsx hsy
  have hpairSlot := AspisR1S9PairCallerStepOperationBridgeV1.map_wide_add x y
  rw [hxy] at hpairSlot
  change Result.ok (AspisR1S9PairCallerStepV1.toP6W z) =
      @AspisR1S9HelperP6.FieldOps.wideAdd
        AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
        (AspisR1S9PairCallerStepV1.toP6W x)
        (AspisR1S9PairCallerStepV1.toP6W y) at hpairSlot
  have hsourceSlot : @AspisR1S9HelperP6.FieldOps.wideAdd
      AspisR1S9ConcreteFieldOpsV1.concreteFieldOps
      (AspisR1S9PairCallerStepV1.toP6W x)
      (AspisR1S9PairCallerStepV1.toP6W y) =
      .ok (AspisR1S9WideAddConcreteMapV1.toHelperWide sz) := by
    simpa [sx, sy, source_to_helper_pair] using hslot
  rw [hsourceSlot] at hpairSlot
  have houtput : AspisR1S9PairCallerStepV1.toP6W z =
      AspisR1S9WideAddConcreteMapV1.toHelperWide sz := Result.ok.inj hpairSlot
  have houtCan := hsourceOutCan
  rw [← houtput] at houtCan
  simpa using houtCan

/-- The exact side-zero three-add output is canonical when its four terms are
canonical and the same suffix execution returned each intermediate sum. -/
theorem pair_four_term_adds_canonical
    (t0 t1 t2 t3 first2 first3 all : W)
    (ht0 : Canonical (AspisR1S9PairCallerStepV1.toP6W t0))
    (ht1 : Canonical (AspisR1S9PairCallerStepV1.toP6W t1))
    (ht2 : Canonical (AspisR1S9PairCallerStepV1.toP6W t2))
    (ht3 : Canonical (AspisR1S9PairCallerStepV1.toP6W t3))
    (h2 : AspisR1S9PairCallerStepV1.field.WideExact.add t0 t1 = .ok first2)
    (h3 : AspisR1S9PairCallerStepV1.field.WideExact.add first2 t2 = .ok first3)
    (ha : AspisR1S9PairCallerStepV1.field.WideExact.add first3 t3 = .ok all) :
    Canonical (AspisR1S9PairCallerStepV1.toP6W first2) ∧
    Canonical (AspisR1S9PairCallerStepV1.toP6W first3) ∧
    Canonical (AspisR1S9PairCallerStepV1.toP6W all) := by
  have hfirst2 := pair_add_success_canonical t0 t1 first2 ht0 ht1 h2
  have hfirst3 := pair_add_success_canonical first2 t2 first3 hfirst2 ht2 h3
  have hall := pair_add_success_canonical first3 t3 all hfirst3 ht3 ha
  exact ⟨hfirst2,hfirst3,hall⟩

#print axioms pair_add_success_canonical
#print axioms pair_four_term_adds_canonical
end AspisR1S9PairAddChainCanonicalV1
