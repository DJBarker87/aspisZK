import NHE_Polynomial
set_option autoImplicit false
namespace NHE_PolynomialDomain
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem go (bytes : Slice U8) (x a out : NE) (is : List Usize)
 (hx : canonE x) (ha : canonE a) (small : ∀ i∈is,i.val<64)
 (run : NHE_HornerPort.go bytes x is a=ok out) : canonE out := by
 induction is generalizing a with
 | nil => exact (Result.ok.inj run.symm) ▸ ha
 | cons i is ih =>
  obtain ⟨product,hp,cp,_⟩ := LPi_TowerValues.wide_mul a x ha hx
  simp only [NHE_HornerPort.go,hp,bind_tc_ok] at run
  obtain ⟨coefficient,hc,rest⟩ := Port3_PushFrame.bind_success _ _ _ run
  have cc := NHE_FieldCanonical.success bytes i (small i (by simp)) coefficient hc
  obtain ⟨next,hn,cn⟩ := NGW_PolynomialAdd.total product coefficient cp cc
  simp only [hn,bind_tc_ok] at rest
  exact ih next cn (fun j hj=>small j (List.mem_cons_of_mem i hj)) rest

theorem source (bytes : Slice U8) (x out : NE) (hx : canonE x)
 (run : NHE_Polynomial.source bytes x=ok out) : canonE out :=
 go bytes x NHE_Polynomial.zero out NHE_Polynomial.indices hx NHE_Polynomial.zero_canonical NHE_Polynomial.indices_small run

#print axioms go
#print axioms source
end NHE_PolynomialDomain
