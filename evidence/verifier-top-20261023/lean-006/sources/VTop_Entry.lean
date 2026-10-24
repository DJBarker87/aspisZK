import VTop_Model
import AdapterRwCuts

set_option autoImplicit false
noncomputable section
namespace AspisR1.VTop_Entry
open Aeneas Aeneas.Std Result VTop_Stages

/-- Install exactly the extracted stage entries as the adapter's external
verifier operations. All other adapter operations stay explicit. -/
def install (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops) : AdapterRw.Ops :=
  { adapter with
    op10 := VTop_Stages.verifier.candidate.tx1 stage
    op11 := VTop_Stages.verifier.candidate.tx2_authenticated stage }

theorem op10_source (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) :
    (install adapter stage).op10 D = VTop_Stages.verifier.candidate.tx1 stage D := rfl

theorem op11_source (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    {Hash : Type} (D : aspis_core.digest.Digest32 Hash) :
    (install adapter stage).op11 D = VTop_Stages.verifier.candidate.tx2_authenticated stage D := rfl

/-- No independent verifier return is introduced by the adapter error map. -/
theorem first_accepted (adapter : AdapterRw.Ops) (stage : VTop_Stages.Ops)
    (semantic : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.first_decoded (install adapter stage) semantic pub proof split = ok (.Ok saved)) :
    VTop_Stages.verifier.candidate.tx1 stage
      (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 (install adapter stage))
      semantic pub proof split () none = ok (.Ok saved) := by
  rw [AdapterRw.Cuts.first_decoded_call] at accepted
  simp only [AdapterRw.core.result.Result.map_err] at accepted
  repeat' first
  | (solve | cases accepted)
  | uncase_result
  | head_reduce accepted
  | split at accepted
  all_goals try simp only [AdapterRw.Cuts.error_bind_ne_ok] at *
  all_goals aesop

#print axioms op10_source
#print axioms op11_source
#print axioms first_accepted
end AspisR1.VTop_Entry
end
