import NNU_QueryFieldCarriers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNU_QueryFieldWide
open Aeneas Aeneas.Std Result AspisR1Stage2
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev K := aspis_core.field.QM31

theorem add (x y : E) : SAQ_Arithmetic.add x y = NBO_FieldSemantics.add x y := by
 have model : NBO_FieldSemantics.add x y =
  (do let a ← (do let z ← AspisR1SelectedMaskProbe.field.QM31.add (NBO_FieldPorts.toQ x.c0) (NBO_FieldPorts.toQ y.c0); ok (NBO_FieldPorts.fromQ z))
      let b ← (do let z ← AspisR1SelectedMaskProbe.field.QM31.add (NBO_FieldPorts.toQ x.c1) (NBO_FieldPorts.toQ y.c1); ok (NBO_FieldPorts.fromQ z))
      ok (⟨a,b⟩ : E)) := by
  simp only [NBO_FieldSemantics.add,NBO_FieldPorts.fromE,bind_assoc_eq,bind_tc_ok]
 rw [model,←NNU_QueryFieldCarriers.addQ,←NNU_QueryFieldCarriers.addQ]
 simp only [SAQ_Arithmetic.add,AspisR1CurrentWide.field.wide_exact.WideExact.add,
  SAQ_WideABI.toW,SAQ_WideABI.fromW,bind_assoc_eq,bind_tc_ok]

theorem mixed (x : E) (q : K) (hq : NBF_PowerStep.Canonical q) :
 SAQ_MixedSource.mulE x q = NBO_FieldSemantics.product x q := by
 have canon : AspisR1CurrentWide.Proof.CanonicalQM (SAQ_WideABI.toQ q) :=
  ⟨⟨hq 0,hq 1⟩,hq 2,hq 3⟩
 have model : NBO_FieldSemantics.product x q =
  (do let a ← NBO_FieldSemantics.power x.c0 q
      let b ← NBO_FieldSemantics.power x.c1 q
      ok (⟨a,b⟩ : E)) := by
  simp only [NBO_FieldSemantics.product,NBO_FieldSemantics.power,NBO_FieldPorts.fromE,
   bind_assoc_eq,bind_tc_ok]
 rw [model,←NNU_QueryFieldCarriers.mulQ,←NNU_QueryFieldCarriers.mulQ]
 simp only [SAQ_MixedSource.mulE,SAQ_MixedSource.source,
  SAQ_MixedSource.canonical_same _ canon,SAQ_Arithmetic.mulK,
  SAQ_WideABI.toW,SAQ_WideABI.fromW,bind_assoc_eq,bind_tc_ok]
#print axioms add
#print axioms mixed
end AspisR1.NNU_QueryFieldWide
end
