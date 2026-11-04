import NFW_PreparedFields
import NFW_QueryStart
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFW_PreparedPort
open Aeneas Aeneas.Std Result
abbrev PQ := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev PE := AspisR1PublicPreparation.aspis_core.field.WideExact
abbrev Q := AspisR1Stage2.aspis_core.field.QM31
abbrev E := AspisR1Stage2.aspis_core.field.wide_exact.WideExact
def q (x : PQ) : Q := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def e (x : PE) : E := ⟨q x.c0,q x.c1⟩
def map {A B : Type} {n : Usize} (f : A→B) (x : Array A n) : Array B n :=
 ⟨x.val.map f,by simpa using x.property⟩
def variant (x : AspisR1PublicPreparation.transport.Variant) : AspisR1Stage2.transport.Variant :=
 match x with | .S1=>.S1 | .S2=>.S2 | .D=>.D
def prepared (p : AspisR1PublicPreparation.verifier.Prepared) : AspisR1Stage2.verifier.Prepared :=
 {variant:=variant p.variant,roots:=p.roots,gamma:=e p.gamma,kappa:=e p.kappa,
  alpha:=map e p.alpha,rho:=q p.rho,queries:=p.queries,semantic_alpha:=map q p.semantic_alpha,
  z:=map (fun z=>⟨q z.x,q z.y⟩) p.z,claim:=e p.claim,state:=p.state}
/-- The query consumer sees the original four raw rho coordinates, with no
independent Prepared output chosen by the transport. -/
theorem rho_canonical (p : AspisR1PublicPreparation.verifier.Prepared)
 (h : p.rho.c0.a.val<2147483647 ∧ p.rho.c0.b.val<2147483647 ∧
      p.rho.c1.a.val<2147483647 ∧ p.rho.c1.b.val<2147483647) :
 NBF_PowerStep.Canonical (prepared p).rho := by
 intro k
 fin_cases k
 · exact h.1
 · exact h.2.1
 · exact h.2.2.1
 · exact h.2.2.2

theorem fields (p : AspisR1PublicPreparation.verifier.Prepared) :
 (prepared p).rho=q p.rho ∧ (prepared p).gamma=e p.gamma ∧
 (prepared p).queries=p.queries ∧ (prepared p).state=p.state ∧
 (prepared p).roots=p.roots ∧ (prepared p).claim=e p.claim := by
 exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
#print axioms rho_canonical
#print axioms fields
end AspisR1.NFW_PreparedPort
