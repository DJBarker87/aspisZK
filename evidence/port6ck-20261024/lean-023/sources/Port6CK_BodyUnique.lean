import Port5Q2_Checkpoint
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port6CK_BodyUnique
open Aeneas Aeneas.Std AspisR1Stage2
open CheckpointBytes4SavedFields

theorem byte_injective : Function.Injective (fun xs : List U8 => MultiproofConeCanonical.bytesOf xs) := by
  intro xs ys same
  apply List.ext_getElem
  · simpa only [MultiproofConeCanonical.bytesOf,List.length_map] using congrArg List.length same
  · intro i hi hj
    apply UScalar.eq_of_val_eq
    have h := congrArg (fun xs => xs[i]?) same
    simpa only [MultiproofConeCanonical.bytesOf,List.getElem?_map,
      List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.map_some,Option.some.injEq] using h

theorem unique (p p1 : verifier.Prepared) (a a1 : verifier.Accumulator)
    (pm : OraclePortCheckpointAbiC5.Prepared)
    (am : QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E)
    (left : BodyMatches p a pm am) (right : BodyMatches p1 a1 pm am)
    (next : a.next.val=a1.next.val) : p=p1 ∧ a=a1 := by
  have state : p.state=p1.state := Subtype.ext (byte_injective (left.state.trans right.state.symm))
  have roots : p.roots=p1.roots := by
    apply Subtype.ext
    apply List.map_injective (fun x y same => Subtype.ext (byte_injective same))
    exact left.roots.trans right.roots.symm
  have alpha : p.alpha=p1.alpha := Subtype.ext (left.alpha.trans right.alpha.symm)
  have queries : p.queries=p1.queries := by
    apply Subtype.ext
    apply List.map_injective (fun x y same => UScalar.eq_of_val_eq same)
    exact left.queries.trans right.queries.symm
  have semantic : p.semantic_alpha=p1.semantic_alpha := Subtype.ext (left.semantic.trans right.semantic.symm)
  have coordinates : p.z=p1.z := by
    obtain ⟨x,y,h⟩ := List.length_eq_two.mp p.z.property
    obtain ⟨x1,y1,h1⟩ := List.length_eq_two.mp p1.z.property
    have same := left.coordinates.trans right.coordinates.symm
    rw [h,h1] at same
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.cons_append,
      List.cons.injEq] at same
    apply Subtype.ext
    rw [h,h1]
    have xx : x=x1 := by cases x; cases x1; simp_all
    have yy : y=y1 := by cases y; cases y1; simp_all
    rw [xx,yy]
  have weights : a.weights=a1.weights := Subtype.ext (left.weights.trans right.weights.symm)
  have pn : a.next=a1.next := UScalar.eq_of_val_eq next
  constructor
  · cases p; cases p1
    simp_all only [verifier.Prepared.mk.injEq]
    exact ⟨left.variant.trans right.variant.symm,state,roots,left.gamma.trans right.gamma.symm,
      left.kappa.trans right.kappa.symm,alpha,left.rho.trans right.rho.symm,queries,semantic,
      coordinates,left.claim.trans right.claim.symm⟩
  · cases a; cases a1
    simp_all only [verifier.Accumulator.mk.injEq]
    exact ⟨weights,left.rhs.trans right.rhs.symm,left.power.trans right.power.symm,pn⟩

#print axioms byte_injective
#print axioms unique
end AspisR1.Port6CK_BodyUnique
end
