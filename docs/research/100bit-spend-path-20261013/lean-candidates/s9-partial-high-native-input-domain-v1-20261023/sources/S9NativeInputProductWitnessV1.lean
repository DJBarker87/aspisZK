import S9ActualEbyKBackendTransportV1
import S4TailFieldProductRootV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeInputProductWitnessV1
open AspisR1S9ActualEbyKBackendTransportV1
abbrev NativePair := NativeW × NativeQ
abbrev SourcePair := AspisR1FastDotsPushProductTraceRootV1.Wide ×
  AspisR1FastDotsPushProductTraceRootV1.QM

def sourcePair (p : NativePair) : SourcePair := (toSourceWide p.1,toSourceQ p.2)
/-- Existing ordered field-product sum, with only the exact coordinate map
on the actual native input pairs. No new arithmetic or dot-meaning contract. -/
def nativeProductSum (ps : List NativePair) : AspisWideTower.WideExact :=
  AspisR1FastDotsTailFieldProductRootV1.productSum (ps.map sourcePair)

/-- Logical witness transport only: retain the actual native pair behind
every source input, preserving source order and both coordinate maps. -/
theorem lift_source_inputs {J : Type} (R : J → NativePair → Prop)
    (js : List J) (xs : List SourcePair)
    (h : List.Forall₂ (fun j p => ∃ t, R j t ∧ p=sourcePair t) js xs) :
    ∃ ys : List NativePair, List.Forall₂ R js ys ∧ xs=ys.map sourcePair := by
  induction h with
  | nil => exact ⟨[],List.Forall₂.nil,rfl⟩
  | @cons j p js xs hp ht ih =>
    obtain ⟨t,hr,hp⟩ := hp
    obtain ⟨ys,hy,hmap⟩ := ih
    subst p
    refine ⟨t::ys,List.Forall₂.cons hr hy,?_⟩
    simp only [List.map_cons,hmap]

#print axioms lift_source_inputs
end AspisR1S9NativeInputProductWitnessV1
