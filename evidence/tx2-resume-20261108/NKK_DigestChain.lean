import NKK_DigestSource
import NKK_Try
set_option autoImplicit false
noncomputable section
namespace NKK_DigestChain
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev Check := Slice (Slice U8) × Slice U8

def source {H T : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) :
 List Check → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error) →
 NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)
 | [],next => next
 | (chunks,stored)::tail,next => NKK_DigestSource.source d hash chunks stored (source d hash tail next)

def model {H T : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H) :
 List Check → NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error) →
 NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)
 | [],next => next
 | (chunks,stored)::tail,next => NKK_DigestSource.model d hash chunks stored (model d hash tail next)

/-- Ordered digest comparisons compose at SAME chunk views and replies.
This source factor is not a native frame or digest-value assumption. -/
theorem source_eq_model {H T : Type} (d : AspisR1Stage2.aspis_core.digest.Digest32 H) (hash : H)
 (checks : List Check) (next : NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result T verifier.Error)) :
 source d hash checks next=model d hash checks next := by
 induction checks with
 | nil => rfl
 | cons check tail ih =>
  rcases check with ⟨chunks,stored⟩
  unfold source model
  rw [NKK_DigestSource.source_eq_model,ih]

#print axioms source_eq_model
end NKK_DigestChain
