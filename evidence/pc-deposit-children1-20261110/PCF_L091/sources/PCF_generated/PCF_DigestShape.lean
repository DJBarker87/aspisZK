import PCF_AppendEncoder
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace PCF_DigestShape

theorem representation (d : Array U32 8#usize) :
    ∃ a b c d' e f g h : U32, d = PCF_DigestFirst.words a b c d' e f g h := by
  rcases d with ⟨xs,hs⟩
  have hlen : xs.length = 8 := hs
  obtain ⟨a,xs0,hx0⟩ := List.exists_cons_of_length_pos (l:=xs) (by omega)
  subst xs
  simp only [List.length_cons] at hlen
  obtain ⟨b,xs1,hx1⟩ := List.exists_cons_of_length_pos (l:=xs0) (by omega)
  subst xs0
  simp only [List.length_cons] at hlen
  obtain ⟨c,xs2,hx2⟩ := List.exists_cons_of_length_pos (l:=xs1) (by omega)
  subst xs1
  simp only [List.length_cons] at hlen
  obtain ⟨d,xs3,hx3⟩ := List.exists_cons_of_length_pos (l:=xs2) (by omega)
  subst xs2
  simp only [List.length_cons] at hlen
  obtain ⟨e,xs4,hx4⟩ := List.exists_cons_of_length_pos (l:=xs3) (by omega)
  subst xs3
  simp only [List.length_cons] at hlen
  obtain ⟨f,xs5,hx5⟩ := List.exists_cons_of_length_pos (l:=xs4) (by omega)
  subst xs4
  simp only [List.length_cons] at hlen
  obtain ⟨g,xs6,hx6⟩ := List.exists_cons_of_length_pos (l:=xs5) (by omega)
  subst xs5
  simp only [List.length_cons] at hlen
  obtain ⟨h,xs7,hx7⟩ := List.exists_cons_of_length_pos (l:=xs6) (by omega)
  subst xs6
  simp only [List.length_cons] at hlen
  have he : xs7 = [] := List.length_eq_zero.mp (by omega)
  subst xs7
  exact ⟨a,b,c,d,e,f,g,h,rfl⟩

theorem encoder (d : Array U32 8#usize) :
    PCB_AppendFullRef.encode_digest_canonical d =
      ok (AspisR1.S2K.DigestBytes.bytes d) := by
  obtain ⟨a,b,c,d',e,f,g,h,rfl⟩ := representation d
  exact PCF_AppendEncoder.words a b c d' e f g h

#print axioms representation
#print axioms encoder
end PCF_DigestShape
