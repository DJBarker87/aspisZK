import NJJ_ResumeDomains
set_option autoImplicit false
noncomputable section
namespace NJJ_Constructors
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem array_ext {T : Type} {n : Usize} (a b : Array T n)
 (cells : ∀ i : Fin n.val, a.val[i.val]?=b.val[i.val]?) : a=b := by
 apply Subtype.ext
 apply List.ext_getElem?
 intro j
 by_cases inside : j<n.val
 · exact cells ⟨j,inside⟩
 · rw [List.getElem?_eq_none (by rw [a.property];omega),
    List.getElem?_eq_none (by rw [b.property];omega)]

def pointCoordinates (p : aspis_core.circle.SecureCirclePoint) := (p.x,p.y)

theorem point_option (a b : Option aspis_core.circle.SecureCirclePoint)
 (same : a.map pointCoordinates=b.map pointCoordinates) : a=b := by
 cases a with
 | none => cases b with | none=>rfl | some p=>cases same
 | some p =>
   cases b with
   | none=>cases same
   | some q=>
     simp only [Option.map_some,Option.some.injEq,pointCoordinates] at same
     cases p
     cases q
     cases same
     rfl

/-- Value part of prepared_tail. Native query/semantic indices are arbitrary;
array_ext assembles all22/10 cells. z equality abbreviates the four native
x/y assertions for its fixed two points, not an unobserved payload. Native
SAME allocation, no-alias and abort ownership remain the (aa) machine cut. -/
structure PreparedCut (before after : verifier.Prepared) : Prop where
 variant : after.variant=before.variant
 roots : after.roots=before.roots
 gamma : after.gamma=before.gamma
 kappa : after.kappa=before.kappa
 alpha : after.alpha=before.alpha
 rho : after.rho=before.rho
 queries : ∀ i : Fin 22,after.queries.val[i.val]?=before.queries.val[i.val]?
 semantic : ∀ i : Fin 10,after.semantic_alpha.val[i.val]?=before.semantic_alpha.val[i.val]?
 z : ∀ i : Fin 2,(after.z.val[i.val]?).map pointCoordinates=(before.z.val[i.val]?).map pointCoordinates
 claim : after.claim=before.claim
 state : after.state=before.state

theorem prepared (before after : verifier.Prepared) (cut : PreparedCut before after) :
 after=before := by
 have queries := array_ext after.queries before.queries cut.queries
 have semantic := array_ext after.semantic_alpha before.semantic_alpha cut.semantic
 have z := array_ext after.z before.z (fun i=>point_option _ _ (cut.z i))
 cases before
 cases after
 cases cut
 simp_all only []

structure AccumulatorCut (before after : verifier.Accumulator) : Prop where
 size : after.weights.val.length=64
 cells : ∀ j, j<64 → after.weights.val[j]?=before.weights.val[j]?
 rhs : after.rhs=before.rhs
 power : after.power=before.power
 next : after.next=before.next

theorem accumulator (before after : verifier.Accumulator)
 (size : before.weights.val.length=64) (cut : AccumulatorCut before after) :
 after=before := by
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

#print axioms array_ext
#print axioms point_option
#print axioms prepared
#print axioms accumulator
end NJJ_Constructors
