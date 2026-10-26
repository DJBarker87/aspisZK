import RPz7_AuS1_Trace
set_option autoImplicit false
noncomputable section
namespace AspisR1.AuS1_Suffix
open Aeneas Aeneas.Std Result
open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1PublicPreparation.PreparedHashCode AuS1_Trace

 theorem right_read {A B : Type} (p : Code A) (k : A → Code B) (out : B)
    (success : erase (p >>= k) = ok out) :
    ∃ a, erase p = ok a ∧ erase (k a) = ok out ∧
      ∀ frame, Read (observe (run (k a)).1) frame → Read (observe (run (p >>= k)).1) frame := by
  obtain ⟨a,hp,hk,logs⟩ := success_bind p k out success
  refine ⟨a,hp,hk,?_⟩
  intro frame read
  rw [logs,observe_append]
  change frame ∈ (observe (run p).1 ++ observe (run (k a)).1).map Prod.fst
  rw [List.map_append]
  exact List.mem_append_right _ read

 theorem left_read {A B : Type} (p : Code A) (k : A → Code B) (out : B)
    (success : erase (p >>= k) = ok out) :
    ∀ frame, Read (observe (run p).1) frame → Read (observe (run (p >>= k)).1) frame := by
  obtain ⟨a,hp,hk,logs⟩ := success_bind p k out success
  intro frame read
  rw [logs,observe_append]
  change frame ∈ (observe (run p).1 ++ observe (run (k a)).1).map Prod.fst
  rw [List.map_append]
  exact List.mem_append_left _ read

#print axioms right_read
#print axioms left_read
end AspisR1.AuS1_Suffix
end
