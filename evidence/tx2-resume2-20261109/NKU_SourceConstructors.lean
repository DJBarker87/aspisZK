import NKU_State
import NJJ_Constructors
set_option autoImplicit false
noncomputable section
namespace NKU_SourceConstructors
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
/-- SAME native prepared_tail assertions as NJJ_Constructors.PreparedCut,
transcribed on the actual NID emitted carrier. No coercion to Stage2 is
assumed. Queries/semantic/z are the arbitrary-index native assertions. -/
structure PreparedCut (before after : verifier.Prepared) : Prop where
 variant : after.variant=before.variant
 roots : after.roots=before.roots
 gamma : after.gamma=before.gamma
 kappa : after.kappa=before.kappa
 alpha : after.alpha=before.alpha
 rho : after.rho=before.rho
 queries : ∀ i : Fin 22,after.queries.val[i.val]?=before.queries.val[i.val]?
 semantic : ∀ i : Fin 10,after.semantic_alpha.val[i.val]?=before.semantic_alpha.val[i.val]?
 z : ∀ i : Fin 2,(after.z.val[i.val]?).map (fun p=>(p.x,p.y))=(before.z.val[i.val]?).map (fun p=>(p.x,p.y))
 claim : after.claim=before.claim
 state : after.state=before.state
theorem point (a b : Option aspis_core.circle.SecureCirclePoint)
 (same : a.map (fun p=>(p.x,p.y))=b.map (fun p=>(p.x,p.y))) : a=b := by
 cases a with
 | none => cases b with | none=>rfl | some p=>cases same
 | some p =>
  cases b with
  | none => cases same
  | some q =>
   simp only [Option.map_some,Option.some.injEq] at same
   cases p
   cases q
   cases same
   rfl
theorem prepared (before after : verifier.Prepared) (cut : PreparedCut before after) : after=before := by
 have queries:=NJJ_Constructors.array_ext after.queries before.queries cut.queries
 have semantic:=NJJ_Constructors.array_ext after.semantic_alpha before.semantic_alpha cut.semantic
 have z:=NJJ_Constructors.array_ext after.z before.z (fun i=>point _ _ (cut.z i))
 cases before
 cases after
 cases cut
 simp_all only []
/-- SAME accumulator assertions and64-cell owner frame on the emitted type. -/
structure AccumulatorCut (before after : verifier.Accumulator) : Prop where
 size : after.weights.val.length=64
 cells : ∀ j,j<64 → after.weights.val[j]?=before.weights.val[j]?
 rhs : after.rhs=before.rhs
 power : after.power=before.power
 next : after.next=before.next
theorem accumulator (before after : verifier.Accumulator)
 (size : before.weights.val.length=64) (cut : AccumulatorCut before after) : after=before := by
 have weights : after.weights=before.weights := by
  apply Subtype.ext
  apply List.ext_getElem?
  intro j
  by_cases inside : j<64
  · exact cut.cells j inside
  · have otherSize:=cut.size
    rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
 cases before
 cases after
 cases cut
 simp_all only []
theorem pair (before after : NKU.Pair) (size : before.2.weights.val.length=64)
 (p : PreparedCut before.1 after.1) (a : AccumulatorCut before.2 after.2) : after=before :=
 Prod.ext (prepared before.1 after.1 p) (accumulator before.2 after.2 size a)
#print axioms point
#print axioms prepared
#print axioms accumulator
#print axioms pair
end NKU_SourceConstructors
