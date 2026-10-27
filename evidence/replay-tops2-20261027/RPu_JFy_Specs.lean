import RPu_JFy_ArrayTotal
import RPu_JFy_Pow5
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFy_Specs
open Aeneas Aeneas.Std Result WP FIq_Native
open FIv_NativeValue (Canon)
open FIw_ArrayValue (canonical)
@[spec] theorem add (x y : field.QM31) (hx : Canon x) (hy : Canon y) :
    field.QM31.add x y ⦃ out => Canon out ⦄ := by
  obtain ⟨out,call,hc,_⟩ := FIv_PreparedTotal.add x y hx hy
  rw [call]
  exact hc
#print axioms add
@[spec] theorem mul (x y : field.QM31) (hx : Canon x) (hy : Canon y) :
    field.QM31.mul x y ⦃ out => Canon out ⦄ := by
  obtain ⟨out,call,hc,_⟩ := JFy_FieldTotal.mul x y hx hy
  rw [call]
  exact hc
#print axioms mul
@[spec] theorem sub (x y : field.QM31) (hx : Canon x) (hy : Canon y) :
    field.QM31.sub x y ⦃ out => Canon out ⦄ := by
  obtain ⟨out,call,hc,_⟩ := JFy_FieldTotal.sub x y hx hy
  rw [call]
  exact hc
#print axioms sub
@[spec] theorem square (x : field.QM31) (hx : Canon x) :
    field.QM31.square x ⦃ out => Canon out ⦄ := by
  obtain ⟨out,call,hc,_⟩ := JFy_SquareTotal.source x hx
  rw [call]
  exact hc
#print axioms square
@[spec] theorem pow5 (x : field.QM31) (hx : Canon x) :
    state_only_poseidon.pow5 x ⦃ out => Canon out ⦄ := by
  obtain ⟨out,call,hc,_⟩ := JFy_Pow5.source x hx
  rw [call]
  exact hc
#print axioms pow5
@[spec] theorem read {N : Usize} (a : Array field.QM31 N) (i : Usize) (bound : i.val<N.val)
    (hc : canonical a) : Array.index_usize a i ⦃ out => Canon out ⦄ := by
  obtain ⟨out,call,hout⟩ := JFy_ArrayTotal.read a i bound hc
  rw [call]
  exact hout
#print axioms read
@[spec] theorem update {N : Usize} (a : Array field.QM31 N) (i : Usize) (x : field.QM31)
    (bound : i.val<N.val) (hc : canonical a) (hx : Canon x) :
    Array.update a i x ⦃ out => canonical out ⦄ := by
  obtain ⟨out,call,hout⟩ := JFy_ArrayTotal.update a i x bound hc hx
  rw [call]
  exact hout
#print axioms update
end AspisR1.JFy_Specs
end
