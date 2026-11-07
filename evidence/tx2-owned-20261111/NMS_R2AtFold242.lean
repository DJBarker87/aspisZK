import NMS_R2N_242Code
set_option autoImplicit false
noncomputable section
namespace NMS_R2AtFold242
open Aeneas Aeneas.Std AdapterRw NMS_R2Refine
abbrev Effects := NMS_R2N_Effect242Fold.Effects
abbrev Auth := NMS_R2N_Effect242Fold.Auth

def identity (effects : Effects) : NMS_R2N_Effect242Fold.Links effects effects := {
 first := fun _ => refl _
 lane := fun _ => refl _
 nullifier := fun _ => refl _
 decode := fun _ => refl _
 pubkey := fun _ => refl _
 pool := refl _
 scan := fun _ => refl _
 reconstruct := fun _ _ _ => refl _
 data := fun _ => refl _
}

/-- The child packet is needed only at the SAME original program/accounts.
No unrelated child-call domain is strengthened to all possible accounts. -/
theorem fold (ops : Ops) (effects : Effects) (auth model : Auth)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (packet : ∀ pool lane current,
   Refines (auth program accounts pool lane current) (model program accounts pool lane current))
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Refines (NMS_R2N_242Code.body effects auth program accounts data slot)
  (NMS_R2N_242Code.body effects model program accounts data slot) := by
 rw [←NMS_R2N_242Code.auth_arguments effects auth program accounts data slot,
   ←NMS_R2N_242Code.auth_arguments effects model program accounts data slot]
 rw [NMS_R2N_242Code.emitted ops,NMS_R2N_242Code.emitted ops]
 exact NMS_R2N_Effect242Fold.fold ops effects effects (identity effects) _ _
  (fun _ _ pool lane current => packet pool lane current) program accounts data slot
/-- Ops-free form for the concrete closed-child interpretation. -/
theorem direct (effects : Effects) (auth model : Auth)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (packet : ∀ pool lane current,
   Refines (auth program accounts pool lane current) (model program accounts pool lane current))
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Refines (NMS_R2N_242Code.body effects auth program accounts data slot)
  (NMS_R2N_242Code.body effects model program accounts data slot) := by
 unfold NMS_R2N_242Code.body
 apply NMS_R2Refine.bind (refl _)
 intro requestSize
 cases hguard : (Slice.len data != requestSize) with
 | false =>
   apply NMS_R2Refine.bind (refl _)
   intro decoded
   apply NMS_R2Refine.bind (refl _)
   intro mappedDecode
   apply NMS_R2Refine.bind (refl _)
   intro flowDecode
   cases flowDecode with
   | Break residual => exact refl _
   | Continue value =>
     apply NMS_R2Refine.bind (refl _)
     intro profileMismatch
     cases hguard : profileMismatch with
     | false =>
       apply NMS_R2Refine.bind (refl _)
       intro releaseMismatch
       cases hguard : releaseMismatch with
       | false =>
         apply NMS_R2Refine.bind (refl _)
         intro poolId
         apply NMS_R2Refine.bind (refl _)
         intro poolMismatch
         cases hguard : poolMismatch with
         | false =>
           apply NMS_R2Refine.bind (refl _)
           intro poolProgram
           apply NMS_R2Refine.bind (refl _)
           intro nullifier
           apply NMS_R2Refine.bind (refl _)
           intro laneReply
           apply NMS_R2Refine.bind (refl _)
           intro mappedLane
           apply NMS_R2Refine.bind (refl _)
           intro flowLane
           cases flowLane with
           | Break residual => exact refl _
           | Continue value =>
             apply NMS_R2Refine.bind (refl _)
             intro flowSlot
             cases flowSlot with
             | Break residual => exact refl _
             | Continue value =>
               apply NMS_R2Refine.bind (packet _ _ _)
               intro authReply
               apply NMS_R2Refine.bind (refl _)
               intro flowAuth
               cases flowAuth with
               | Break residual => exact refl _
               | Continue value =>
                 apply NMS_R2Refine.bind (refl _)
                 intro firstAccount
                 apply NMS_R2Refine.bind (refl _)
                 intro accountReply
                 apply NMS_R2Refine.bind (refl _)
                 intro flowAccount
                 cases flowAccount with
                 | Break residual => exact refl _
                 | Continue value =>
                   apply NMS_R2Refine.bind (refl _)
                   intro read
                   apply NMS_R2Refine.bind (refl _)
                   intro flowData
                   cases flowData with
                   | Break residual => exact refl _
                   | Continue value =>
                     apply NMS_R2Refine.bind (refl _)
                     intro scanner
                     apply NMS_R2Refine.bind (refl _)
                     intro flowScanner
                     cases flowScanner with
                     | Break residual => exact refl _
                     | Continue value =>
                       apply NMS_R2Refine.bind (refl _)
                       intro reconstruction
                       apply NMS_R2Refine.bind (refl _)
                       intro flowStatement
                       cases flowStatement with
                       | Break residual => exact refl _
                       | Continue value =>
                         exact refl _
         | true => exact refl _
       | true => exact refl _
     | true => exact refl _
 | true => exact refl _

#print axioms fold
#print axioms direct
end NMS_R2AtFold242
