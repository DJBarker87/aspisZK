import NHE_FieldCanonical
import NGW_Horner
set_option autoImplicit false
namespace NHE_HornerPort
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

def go (bytes : Slice U8) (x : NE) : List Usize → NE → Result NE
 | [],a => ok a
 | i::is,a => do
   let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul a x
   let coefficient ← FIo_Native.weights.field bytes i
   let next ← FIo_Native.aspis_core.field.wide_exact.WideExact.add product coefficient
   go bytes x is next

theorem adopted (bytes : Slice U8) (x a : NE) (is : List Usize)
 (hx : canonE x) (ha : canonE a) (small : ∀ i∈is,i.val<64) :
 FIo_FieldBridge.map FIo_Install.fromE (go bytes x is a)=
 FIn_Polynomial.go bytes (FIo_Install.fromE x) is (FIo_Install.fromE a) := by
 induction is generalizing a with
 | nil => rfl
 | cons i is ih =>
  obtain ⟨product,hp,cp,_⟩ := LPi_TowerValues.wide_mul a x ha hx
  have pm := NHE_WidePort.adopted a x ha hx
  rw [hp] at pm
  change ok (FIo_Install.fromE product)=_ at pm
  have fp := NHE_FieldPort.adopted bytes i (small i (by simp))
  simp only [go,FIn_Polynomial.go,←pm,hp,bind_tc_ok,←fp,FIo_FieldBridge.map_bind]
  cases hc : FIo_Native.weights.field bytes i with
  | fail e => rfl
  | div => rfl
  | ok coefficient =>
   have cc := NHE_FieldCanonical.success bytes i (small i (by simp)) coefficient hc
   obtain ⟨next,hn,cn⟩ := NGW_PolynomialAdd.total product coefficient cp cc
   have ap := NGW_CurrentAddPort.adopted product coefficient cp cc
   rw [hn] at ap
   change ok (FIo_Install.fromE next)=_ at ap
   simp only [FIo_FieldBridge.map,bind_tc_ok,←ap,hn]
   exact ih next cn (fun j hj=>small j (List.mem_cons_of_mem i hj))

#print axioms adopted
end NHE_HornerPort
