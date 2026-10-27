import RPz7_S1QueryMaterializeModelV1
set_option autoImplicit false
noncomputable section
namespace AspisR1PublicPreparation.PreparedQueryMaterialize
open Aeneas Aeneas.Std Result
open AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- TOTAL length-checked conversion preserves BOTH complete buffers in order.
Its panic arm is unreachable at the lengths returned by the fixed chain. -/
theorem packEight_exact (bs xs : List State) (hbs : bs.length=8) (hxs : xs.length=8) :
    ∃ (blocks advances : Blocks8),packEight bs xs=ok (blocks,advances) ∧
      blocks.val.map decodeState=bs ∧ advances.val.map decodeState=xs := by
  obtain ⟨b0,bs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<bs.length)
  simp only [List.length_cons] at hbs
  obtain ⟨b1,bs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<bs.length)
  simp only [List.length_cons] at hbs
  obtain ⟨b2,bs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<bs.length)
  simp only [List.length_cons] at hbs
  obtain ⟨b3,bs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<bs.length)
  simp only [List.length_cons] at hbs
  obtain ⟨b4,bs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<bs.length)
  simp only [List.length_cons] at hbs
  obtain ⟨b5,bs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<bs.length)
  simp only [List.length_cons] at hbs
  obtain ⟨b6,bs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<bs.length)
  simp only [List.length_cons] at hbs
  obtain ⟨b7,bs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<bs.length)
  simp only [List.length_cons] at hbs
  have emptyb : bs=[] := List.eq_nil_of_length_eq_zero (by omega)
  subst bs
  obtain ⟨x0,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<xs.length)
  simp only [List.length_cons] at hxs
  obtain ⟨x1,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<xs.length)
  simp only [List.length_cons] at hxs
  obtain ⟨x2,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<xs.length)
  simp only [List.length_cons] at hxs
  obtain ⟨x3,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<xs.length)
  simp only [List.length_cons] at hxs
  obtain ⟨x4,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<xs.length)
  simp only [List.length_cons] at hxs
  obtain ⟨x5,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<xs.length)
  simp only [List.length_cons] at hxs
  obtain ⟨x6,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<xs.length)
  simp only [List.length_cons] at hxs
  obtain ⟨x7,xs,rfl⟩ := List.exists_cons_of_length_pos (by omega : 0<xs.length)
  simp only [List.length_cons] at hxs
  have emptyx : xs=[] := List.eq_nil_of_length_eq_zero (by omega)
  subst xs
  exact ⟨_,_,rfl,by simp only [Array.make,List.map_cons,List.map_nil,state_roundtrip],
    by simp only [Array.make,List.map_cons,List.map_nil,state_roundtrip]⟩

#print axioms packEight_exact
end AspisR1PublicPreparation.PreparedQueryMaterialize
