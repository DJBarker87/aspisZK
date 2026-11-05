import NHF_ViewWindows
set_option autoImplicit false
namespace AspisR1.NHF_ByteAssembly
open Aeneas Aeneas.Std NHF_ViewWindows
/-- Symbolic radix join; no enumeration over words or field elements. -/
theorem mod_div_join (x y base : Nat) (low : x%base=y%base) (high : x/base=y/base) : x=y := by
 calc
  x=x%base+base*(x/base) := (Nat.mod_add_div x base).symm
  _=y%base+base*(y/base) := by rw [low,high]
  _=y := Nat.mod_add_div y base
/-- Four byte observations identify every u32, including noncanonical words. -/
theorem word (x y : Nat) (hx : x<4294967296) (hy : y<4294967296)
 (same : ∀ i,i<4→x/256^i%256=y/256^i%256) : x=y := by
 have h0:=same 0 (by omega)
 have h1:=same 1 (by omega)
 have h2:=same 2 (by omega)
 have h3:=same 3 (by omega)
 norm_num at h0 h1 h2 h3
 have eq3 : x/16777216=y/16777216 := by omega
 have div2x : (x/65536)/256=x/16777216 := by rw [Nat.div_div_eq_div_mul];rfl
 have div2y : (y/65536)/256=y/16777216 := by rw [Nat.div_div_eq_div_mul];rfl
 have eq2 : x/65536=y/65536 := mod_div_join _ _ 256 h2 (by rw [div2x,div2y];exact eq3)
 have div1x : (x/256)/256=x/65536 := by rw [Nat.div_div_eq_div_mul];rfl
 have div1y : (y/256)/256=y/65536 := by rw [Nat.div_div_eq_div_mul];rfl
 have eq1 : x/256=y/256 := mod_div_join _ _ 256 h1 (by rw [div1x,div1y];exact eq2)
 exact mod_div_join x y 256 h0 eq1

def byteAt (x : E) (i : Fin 32) : Nat :=
 (coordinate x ⟨i.val/4,by omega⟩).val / 256^(i.val%4) % 256

theorem at_word (x : E) (w : Fin 8) (j : Fin 4) :
 byteAt x ⟨4*w.val+j.val,by omega⟩ = (coordinate x w).val/256^j.val%256 := by
 have hd : (4*w.val+j.val)/4=w.val := by omega
 have hm : (4*w.val+j.val)%4=j.val := by omega
 simp only [byteAt,hd,hm]

/-- All32 arbitrary-byte windows identify the SAME returned E record. -/
theorem injective (x y : E) (same : ∀ i,byteAt x i=byteAt y i) : x=y := by
 apply NHF_ViewWindows.injective x y
 intro w
 apply UScalar.eq_of_val_eq
 apply word
 · scalar_tac
 · scalar_tac
 · intro i hi
   have eq:=same ⟨4*w.val+i,by omega⟩
   have a:=at_word x w ⟨i,hi⟩
   have b:=at_word y w ⟨i,hi⟩
   rw [a,b] at eq
   exact eq
#print axioms mod_div_join
#print axioms word
#print axioms at_word
#print axioms injective
end AspisR1.NHF_ByteAssembly
