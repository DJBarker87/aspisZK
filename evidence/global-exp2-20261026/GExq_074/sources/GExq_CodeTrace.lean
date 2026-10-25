import GExp_RunPrefix
import GExq_OuterLower
set_option autoImplicit false
noncomputable section
namespace AspisR1.GExq_CodeTrace
open Aeneas Aeneas.Std Result CheckpointBytes5Effect
open FS2.Duplex

theorem success_bind {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Code A) (k : A → Code B) (out : B)
    (success : erase (SdkC_Source.dictionary hashv) () (CheckpointBytes5Effect.bind p k) = ok out) :
    ∃ a, erase (SdkC_Source.dictionary hashv) () p = ok a ∧
      erase (SdkC_Source.dictionary hashv) () (k a) = ok out ∧
      SdkC_Source.readLog (SdkC_Source.run hashv (CheckpointBytes5Effect.bind p k) []).2 =
        SdkC_Source.readLog (SdkC_Source.run hashv p []).2 ++
        SdkC_Source.readLog (SdkC_Source.run hashv (k a) []).2 := by
  rw [GExq_OuterLower.erase_bind_explicit] at success
  cases hp : erase (SdkC_Source.dictionary hashv) () p with
  | fail e => simp only [hp,bind_tc_fail] at success; cases success
  | div => simp only [hp,bind_tc_div] at success; cases success
  | ok a =>
    simp only [hp,bind_tc_ok] at success
    refine ⟨a,rfl,success,?_⟩
    have runLaw := SdkC_Source.run_bind hashv p k []
    have native : (SdkC_Source.run hashv p []).1 = ok a := (SdkC_Source.erasure hashv p []).trans hp
    change SdkC_Source.run hashv (CheckpointBytes5Effect.bind p k) [] = _ at runLaw
    rw [runLaw]
    simp only [SdkC_Source.resume,native]
    have shifted := GExp_RunPrefix.run_append hashv (k a) (SdkC_Source.run hashv p []).2 []
    simp only [List.append_nil] at shifted
    rw [shifted,SdkC_Oracle.readLog_append]

theorem left_read {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Code A) (k : A → Code B) (out : B)
    (success : erase (SdkC_Source.dictionary hashv) () (CheckpointBytes5Effect.bind p k) = ok out)
    (frame : AspisV8R19.DuplexFrames.Bytes)
    (read : Read (SdkC_Source.readLog (SdkC_Source.run hashv p []).2) frame) :
    Read (SdkC_Source.readLog (SdkC_Source.run hashv (CheckpointBytes5Effect.bind p k) []).2) frame := by
  obtain ⟨a,_,_,logs⟩ := success_bind hashv p k out success
  rw [logs]
  change frame ∈ (SdkC_Source.readLog (SdkC_Source.run hashv p []).2 ++
    SdkC_Source.readLog (SdkC_Source.run hashv (k a) []).2).map Prod.fst
  rw [List.map_append]
  exact List.mem_append_left _ read

theorem right_read {A B : Type} (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
    (p : Code A) (k : A → Code B) (out : B)
    (success : erase (SdkC_Source.dictionary hashv) () (CheckpointBytes5Effect.bind p k) = ok out) :
    ∃ a, erase (SdkC_Source.dictionary hashv) () p = ok a ∧
      erase (SdkC_Source.dictionary hashv) () (k a) = ok out ∧
      ∀ frame, Read (SdkC_Source.readLog (SdkC_Source.run hashv (k a) []).2) frame →
        Read (SdkC_Source.readLog (SdkC_Source.run hashv (CheckpointBytes5Effect.bind p k) []).2) frame := by
  obtain ⟨a,hp,hk,logs⟩ := success_bind hashv p k out success
  refine ⟨a,hp,hk,?_⟩
  intro frame read
  rw [logs]
  change frame ∈ (SdkC_Source.readLog (SdkC_Source.run hashv p []).2 ++
    SdkC_Source.readLog (SdkC_Source.run hashv (k a) []).2).map Prod.fst
  rw [List.map_append]
  exact List.mem_append_right _ read

#print axioms success_bind
#print axioms left_read
#print axioms right_read
end AspisR1.GExq_CodeTrace
end
