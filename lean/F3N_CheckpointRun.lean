import CheckpointBytes5Effect
import OraclePortCkptAbiTry
set_option autoImplicit false
namespace AspisR1.F3N_CheckpointRun
open Aeneas Aeneas.Std Result AspisR1Stage2 CheckpointBytes5Effect

theorem exists_run {A Hash : Type} (D : aspis_core.digest.Digest32 Hash) (hash : Hash)
    (c : Code A) (out : A) (before : Log) (success : erase D hash c=ok out) :
    ∃ after,run D hash c before=ok (out,after) := by
  induction c generalizing before with
  | done value =>
    have same : value=out := Result.ok.inj success
    subst value
    exact ⟨before,rfl⟩
  | step result next ih =>
    obtain ⟨value,called,rest⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
    obtain ⟨after,ran⟩ := ih value before rest
    exact ⟨after,by simp only [run,called,bind_tc_ok];exact ran⟩
  | read parts next ih =>
    obtain ⟨digest,called,rest⟩ := OraclePortCkptAbiTry.bind_success _ _ _ success
    obtain ⟨after,ran⟩ := ih digest (before++[(parts,digest)]) rest
    exact ⟨after,by simp only [run,called,bind_tc_ok];exact ran⟩

#print axioms exists_run
end AspisR1.F3N_CheckpointRun
