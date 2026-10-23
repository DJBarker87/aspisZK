import CheckpointBytes5Effect

/-! The one-read contract derived from the existing effect interpreter.
No native hashv interpretation, ideal oracle law or native reification assumed. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2G.Digest
open AspisR1.CheckpointBytes5Effect

theorem contract {H : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (hash : H) (parts : Parts) (before : Log) :
    run D hash (read parts) before =
      (do let digest ← D.digest hash parts; ok (digest,before ++ [(parts,digest)])) :=
  run_read D hash parts before

/-- Each digest substitution must retain this event, even when its continuation
later returns an inner verifier Err. No successful-child conditioning here. -/
theorem reached_call {H A : Type} (D : AspisR1Stage2.aspis_core.digest.Digest32 H)
    (hash : H) (parts : Parts) (before : Log) (digest : Digest) (next : Digest → Code A)
    (returned : D.digest hash parts = ok digest) :
    run D hash (read parts >>= next) before =
      run D hash (next digest) (before ++ [(parts,digest)]) := by
  rw [run_bind,run_read,returned]
  rfl

#print axioms contract
#print axioms reached_call
end AspisR1.S2G.Digest
