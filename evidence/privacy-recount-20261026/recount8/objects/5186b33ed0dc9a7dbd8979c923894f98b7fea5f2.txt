import R1Z.PV_RunJoin_RecordPost43
set_option autoImplicit false
namespace R1Z.PV_RunJoin_ByteExtension43
open Aeneas Aeneas.Std

def Ext (before after : List U8) (n : Nat) : Prop :=
  ∃ tail, tail.length=n ∧ after=before++tail

theorem refl (bytes : List U8) : Ext bytes bytes 0 := ⟨[],rfl,by simp⟩

theorem trans {a b c : List U8} {n m : Nat} (h : Ext a b n) (k : Ext b c m) :
    Ext a c (n+m) := by
  obtain ⟨x,hx,hb⟩ := h
  obtain ⟨y,hy,hc⟩ := k
  exact ⟨x++y,by simp only [List.length_append,hx,hy],by rw [hc,hb,List.append_assoc]⟩

theorem length {a b : List U8} {n : Nat} (h : Ext a b n) : b.length=a.length+n := by
  obtain ⟨tail,ht,hb⟩ := h
  rw [hb,List.length_append,ht]

#print axioms refl
#print axioms trans
#print axioms length
end R1Z.PV_RunJoin_ByteExtension43
