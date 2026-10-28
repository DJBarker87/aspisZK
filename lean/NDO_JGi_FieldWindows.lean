import NDO_JGe_Payload27
set_option autoImplicit false
namespace AspisR1.JGi_FieldWindows
open Aeneas Aeneas.Std Result

theorem source {A : Type} (xs : List (List A)) (lengths : ∀ c∈xs,c.length=32)
    (i : Nat) (bound : i<xs.length) :
    (xs.flatten.drop (32*i)).take 32=xs[i]'bound := by
  induction xs generalizing i with
  | nil => simp at bound
  | cons head tail ih =>
    have hl : head.length=32 := lengths head (by simp)
    have tl : ∀ c∈tail,c.length=32 := by intro c hc;exact lengths c (by simp only [List.mem_cons];exact Or.inr hc)
    cases i with
    | zero =>
      simp only [Nat.mul_zero,List.drop_zero,List.flatten_cons,List.getElem_cons_zero,List.take_append,
        hl,show 32-32=0 from rfl,List.take_zero,List.append_nil]
      exact List.take_of_length_le (by omega)
    | succ i =>
      rw [List.flatten_cons,List.drop_append,hl]
      rw [List.drop_eq_nil_of_le (by rw [hl];omega),List.nil_append]
      rw [show 32*(i+1)-32=32*i from by omega]
      exact ih tl i (by simpa using bound)
#print axioms source

theorem lengths : ∀ c∈JGe_Payload27.sourceChunks,c.length=32 := by
  intro c hc
  simp only [JGe_Payload27.sourceChunks,List.mem_map] at hc
  obtain ⟨r,hr,rfl⟩ := hc
  simp only [List.length_append,JGe_Payload27.lengths r hr,List.length_replicate]
#print axioms lengths

theorem selected (i : Nat) (hi : i<29) :
    (JGe_Payload27.value.val.drop (32*i)).take 32=
      JGe_Payload27.sourceChunks[i]'(by change i<29;exact hi) := by
  rw [JGe_Payload27.bytes]
  exact source _ lengths i (by change i<29;exact hi)
#print axioms selected
end AspisR1.JGi_FieldWindows
