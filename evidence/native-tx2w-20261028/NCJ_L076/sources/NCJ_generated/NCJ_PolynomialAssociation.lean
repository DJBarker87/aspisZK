import NCJ_PolynomialTotal
import NCJ_CarrierPorts
import FIn_ExtractInstall
set_option autoImplicit false
noncomputable section
namespace NCJ_PolynomialAssociation
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev cast := FIo_Install.fromE
abbrev mapped := FIo_FieldBridge.map cast

/-- Structural same-byte association. The three exact primitive ports are
explicit lower obligations, restricted to canonical operands and reached reads.
There is no assumed whole-polynomial result. -/
theorem go (bytes : Slice U8) (x a : NE) (hx : canonE x) (ha : canonE a)
    (is : List Usize) (valid : ∀ i∈is,NCJ_HornerBytes.Valid bytes i)
    (mulPort : ∀ p q,canonE p → canonE q →
      mapped (FIo_Native.aspis_core.field.wide_exact.WideExact.mul p q)=
        FIn_Polynomial.mul (cast p) (cast q))
    (addPort : ∀ p q,canonE p → canonE q →
      mapped (FIo_Native.aspis_core.field.wide_exact.WideExact.add p q)=
        FIn_Primitives.add (cast p) (cast q))
    (readPort : ∀ i∈is,mapped (FIo_Native.weights.field bytes i)=FIn_Primitives.field bytes i) :
    ∃ out,NCJ_HornerBytes.go bytes x is a=ok out ∧ canonE out ∧
      FIn_Polynomial.go bytes (cast x) is (cast a)=ok (cast out) := by
  induction is generalizing a with
  | nil => exact ⟨a,rfl,ha,rfl⟩
  | cons i is ih =>
    obtain ⟨p,hp,cp,_⟩ := LPi_TowerValues.wide_mul a x ha hx
    have vi:=valid i (by simp)
    obtain ⟨part,_,hc,cc⟩ := NCJ_FieldTotal.source bytes i vi.1 vi.2
    obtain ⟨next,hn,cn,_⟩ := NBG_WideCarriers.wide_add p (NCJ_FieldTotal.decode part) cp cc
    obtain ⟨out,run,co,assoc⟩ := ih next cn (fun j hj=>valid j (by simp [hj]))
      (fun j hj=>readPort j (by simp [hj]))
    have mp : FIn_Polynomial.mul (cast a) (cast x)=ok (cast p) := by
      rw [←mulPort a x ha hx,hp];rfl
    have mc : FIn_Primitives.field bytes i=ok (cast (NCJ_FieldTotal.decode part)) := by
      rw [←readPort i (by simp),hc];rfl
    have mn : FIn_Primitives.add (cast p) (cast (NCJ_FieldTotal.decode part))=ok (cast next) := by
      rw [←addPort p _ cp cc,hn];rfl
    exact ⟨out,by simp only [NCJ_HornerBytes.go,hp,hc,hn,run,bind_tc_ok],co,
      by simp only [FIn_Polynomial.go,mp,mc,mn,assoc,bind_tc_ok]⟩

theorem polynomial (bytes : Slice U8) (domain : NCJ_PolynomialTotal.Domain bytes)
    (x : NE) (hx : canonE x)
    (mulPort : ∀ p q,canonE p → canonE q → mapped
      (FIo_Native.aspis_core.field.wide_exact.WideExact.mul p q)=FIn_Polynomial.mul (cast p) (cast q))
    (addPort : ∀ p q,canonE p → canonE q → mapped
      (FIo_Native.aspis_core.field.wide_exact.WideExact.add p q)=FIn_Primitives.add (cast p) (cast q))
    (readPort : ∀ i∈NCJ_PolynomialTotal.indices,
      mapped (FIo_Native.weights.field bytes i)=FIn_Primitives.field bytes i) :
    ∃ out,NCJ_HornerBytes.go bytes x NCJ_PolynomialTotal.indices
        FIo_Native.aspis_core.field.wide_exact.WideExact.ZERO=ok out ∧ canonE out ∧
      FIn_Polynomial.polynomial bytes (cast x)=ok (cast out) ∧
      FIn_ExtractInstall.polynomial bytes (cast x)=ok (cast out) := by
  have valid : ∀ i∈NCJ_PolynomialTotal.indices,NCJ_HornerBytes.Valid bytes i := by
    intro i hi
    have b:=NCJ_PolynomialTotal.index_bound i hi
    exact ⟨by rw [domain.1];omega,domain.2 i b⟩
  obtain ⟨out,run,co,assoc⟩ := go bytes x _ hx NCJ_Constants.zero _ valid mulPort addPort readPort
  have model : FIn_Polynomial.polynomial bytes (cast x)=ok (cast out) := assoc
  exact ⟨out,run,co,model,by rw [FIn_ExtractInstall.same];exact model⟩
#print axioms go
#print axioms polynomial
end NCJ_PolynomialAssociation
