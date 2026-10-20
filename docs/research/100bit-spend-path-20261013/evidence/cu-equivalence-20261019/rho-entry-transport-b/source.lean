import CuSavingsRhoPrepared
import CuSavingsRhoAccumulatorCanonical
import CuSavingsRhoStage
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoEntryTransport
open Aeneas Aeneas.Std Result
namespace T
abbrev K := AspisR1RhoPowerTail.aspis_core.field.QM31
abbrev E := AspisR1RhoPowerTail.aspis_core.field.WideExact
abbrev Point := AspisR1RhoPowerTail.aspis_core.circle.SecureCirclePoint
abbrev Prep := AspisR1RhoPowerTail.verifier.Prepared
abbrev Acc := AspisR1RhoPowerTail.verifier.Accumulator
end T
namespace Q
abbrev K := AspisR1RhoQuery.aspis_core.field.QM31
abbrev E := AspisR1RhoQuery.aspis_core.field.WideExact
abbrev Point := AspisR1RhoQuery.aspis_core.circle.SecureCirclePoint
abbrev Prep := AspisR1RhoQuery.verifier.Prepared
abbrev Acc := AspisR1RhoQuery.verifier.Accumulator
end Q

def scalar (x : T.K) : Q.K :=
  {c0:={a:=x.c0.a,b:=x.c0.b},c1:={a:=x.c1.a,b:=x.c1.b}}
def wide (x : T.E) : Q.E := {c0:=scalar x.c0,c1:=scalar x.c1}
def point (x : T.Point) : Q.Point := {x:=scalar x.x,y:=scalar x.y}
def array {A B : Type} {n : Usize} (f : A → B) (xs : Array A n) : Array B n :=
  ⟨xs.val.map f,by simpa only [List.length_map] using xs.property⟩
def vector (xs : alloc.vec.Vec T.K) : alloc.vec.Vec Q.K :=
  ⟨xs.val.map scalar,by simpa only [List.length_map] using xs.property⟩
def prepared (p : T.Prep) : Q.Prep :=
  {variant:=p.variant,roots:=p.roots,gamma:=wide p.gamma,kappa:=wide p.kappa,
   alpha:=array wide p.alpha,rho:=scalar p.rho,queries:=p.queries,
   semantic_alpha:=array scalar p.semantic_alpha,z:=array point p.z,
   claim:=wide p.claim,state:=p.state}
def accumulator (a : T.Acc) : Q.Acc :=
  {weights:=vector a.weights,rhs:=wide a.rhs,power:=scalar a.power,next:=a.next}

theorem scalar_canonical (x : T.K) (hc : CuSavingsRhoPowerTail.Canonical x) :
    CuSavingsRhoInitRow.Canonical (scalar x) := by
  intro i
  fin_cases i <;> first | exact hc.1.1 | exact hc.1.2 | exact hc.2.1 | exact hc.2.2

theorem vector_canonical (xs : alloc.vec.Vec T.K)
    (hc : ∀ (i : Nat) (hi : i<xs.val.length),CuSavingsRhoPowerTail.Canonical (xs.val[i]'hi)) :
    CuSavingsRhoResumeLoans.CanonicalFrom (vector xs) 0 := by
  intro i hi _
  change CuSavingsRhoInitRow.Canonical ((xs.val.map scalar)[i]'hi)
  rw [List.getElem_map]
  exact scalar_canonical _ (hc i (by simpa only [vector,List.length_map] using hi))

/-- Coordinate-only carrier aliases transport the successful whole source
constructor into exactly the stage's initial canonicality and length premises. -/
theorem constructor_inputs (backend : CuSavingsRhoEmptyReserveModel.Backend)
    (variant : AspisR1RhoPowerTail.transport.Variant) (out : T.Acc)
    (h : @AspisR1RhoPowerTail.verifier.Accumulator.new
      (CuSavingsRhoEmptyReserveModel.heapReserve backend) variant = .ok (.Ok out)) :
    CuSavingsRhoResumeLoans.CanonicalFrom (accumulator out).weights 0 ∧
    CuSavingsRhoInitRow.Canonical (accumulator out).power ∧
    (alloc.vec.Vec.len (accumulator out).weights).val ≤ 256 := by
  letI : AspisR1CuRho.HeapReserve := CuSavingsRhoEmptyReserveModel.heapReserve backend
  obtain ⟨_,hc⟩ := CuSavingsRhoAccumulatorCanonical.source_values backend variant out h
  obtain ⟨_,hpower,_,_,hlen,_⟩ := CuSavingsRhoAccumulatorNew.source_success variant out h
  refine ⟨vector_canonical out.weights hc,scalar_canonical out.power hpower,?_⟩
  simpa only [accumulator,vector,alloc.vec.Vec.len,Slice.len_val,Slice.length,List.length_map] using hlen

variable [AspisR1RhoPowerTail.PreparedCommon] [AspisR1CuRho.ScalarKBlocks]
/-- Stored rho canonicality is derived from the actual whole preparation call. -/
theorem preparation_input {H : Type} (D : AspisR1RhoPowerTail.aspis_core.Digest32 H)
    (sem : AspisR1RhoPowerTail.r1_semantic.Verified H)
    (v : AspisR1RhoPowerTail.verifier.View) (hash : H)
    (scratch finalScratch : Array T.E 29#usize) (out : T.Prep)
    (h : AspisR1RhoPowerTail.gamma_new.Prepared.gamma_new_new D sem v hash scratch =
      .ok (.Ok out,finalScratch)) :
    CuSavingsRhoInitRow.Canonical (prepared out).rho := by
  exact scalar_canonical out.rho (CuSavingsRhoPrepared.source_success D sem v hash scratch finalScratch out h).1

#print axioms scalar_canonical
#print axioms vector_canonical
#print axioms constructor_inputs
#print axioms preparation_input
end AspisR1.CuSavingsRhoEntryTransport
