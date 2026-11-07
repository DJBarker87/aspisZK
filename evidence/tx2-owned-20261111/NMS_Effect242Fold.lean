import NMS_Interpreted
set_option autoImplicit false
noncomputable section
namespace NMS_Effect242Fold
open Aeneas Aeneas.Std AdapterRw NMS_RSLRefine
abbrev Effects := NMS_Effect242.Effects RSL.Spec
abbrev Auth := NMS_Effect242.AuthCall RSL.Spec
/-- Every link is a COMPLETE child observation law, at identical typed
arguments. The dictionary is intermediate source composition, not a native
root with arbitrary operations. CLOSED links still require installation. -/
structure Links (actual model : Effects) : Prop where
 first : ∀ {T : Type} (a : Slice T), Refines (actual.op9 a) (model.op9 a)
 lane : ∀ n, Refines (actual.op17 n) (model.op17 n)
 nullifier : ∀ p, Refines (actual.op20 p) (model.op20 p)
 decode : ∀ d, Refines (actual.op23 d) (model.op23 d)
 pubkey : ∀ p, Refines (actual.op37 p) (model.op37 p)
 pool : Refines actual.op45 model.op45
 scan : ∀ d, Refines (actual.op51 d) (model.op51 d)
 reconstruct : ∀ r a c, Refines (actual.op52 r a c) (model.op52 r a c)
 data : ∀ a, Refines (actual.data a) (model.data a)

def AuthLink (actual model : Auth) : Prop :=
 ∀ p a pool lane slot, Refines (actual p a pool lane slot) (model p a pool lane slot)

/-- Actual emitted control, with complete child laws substituted forward.
Returned errors, fail/div, independent stops and every ordered event prefix
are all quantified in Refines; no successful child premise is used. -/
theorem fold (ops : Ops) (actual model : Effects) (children : Links actual model)
 (auth referenceAuth : Auth) (child233 : AuthLink auth referenceAuth)
 (program : solana_pubkey.Pubkey) (accounts : Slice r1_pool_adapter.owned.OwnedAccount)
 (data : Slice U8) (slot : core.result.Result U64 solana_program_error.ProgramError) :
 Refines (NMS_Effect242.validate ops actual auth program accounts data slot)
  (NMS_Effect242.validate ops model referenceAuth program accounts data slot) := by
 unfold NMS_Effect242.validate
 apply NMS_RSLRefine.bind (refl _)
 intro requestSize
 cases hguard : (Slice.len data != requestSize) with
 | false =>
   apply NMS_RSLRefine.bind (children.decode _)
   intro decoded
   apply NMS_RSLRefine.bind (refl _)
   intro mappedDecode
   apply NMS_RSLRefine.bind (refl _)
   intro flowDecode
   cases flowDecode with
   | Break residual => exact refl _
   | Continue value =>
     apply NMS_RSLRefine.bind (refl _)
     intro profileMismatch
     cases hguard : profileMismatch with
     | false =>
       apply NMS_RSLRefine.bind (refl _)
       intro releaseMismatch
       cases hguard : releaseMismatch with
       | false =>
         apply NMS_RSLRefine.bind (children.pool)
         intro poolId
         apply NMS_RSLRefine.bind (refl _)
         intro poolMismatch
         cases hguard : poolMismatch with
         | false =>
           apply NMS_RSLRefine.bind (children.pubkey _)
           intro poolProgram
           apply NMS_RSLRefine.bind (children.nullifier _)
           intro nullifier
           apply NMS_RSLRefine.bind (children.lane _)
           intro laneReply
           apply NMS_RSLRefine.bind (refl _)
           intro mappedLane
           apply NMS_RSLRefine.bind (refl _)
           intro flowLane
           cases flowLane with
           | Break residual => exact refl _
           | Continue value =>
             apply NMS_RSLRefine.bind (refl _)
             intro flowSlot
             cases flowSlot with
             | Break residual => exact refl _
             | Continue value =>
               apply NMS_RSLRefine.bind (child233 _ _ _ _ _)
               intro authReply
               apply NMS_RSLRefine.bind (refl _)
               intro flowAuth
               cases flowAuth with
               | Break residual => exact refl _
               | Continue value =>
                 apply NMS_RSLRefine.bind (children.first _)
                 intro firstAccount
                 apply NMS_RSLRefine.bind (refl _)
                 intro accountReply
                 apply NMS_RSLRefine.bind (refl _)
                 intro flowAccount
                 cases flowAccount with
                 | Break residual => exact refl _
                 | Continue value =>
                   apply NMS_RSLRefine.bind (children.data _)
                   intro read
                   apply NMS_RSLRefine.bind (refl _)
                   intro flowData
                   cases flowData with
                   | Break residual => exact refl _
                   | Continue value =>
                     apply NMS_RSLRefine.bind (children.scan _)
                     intro scanner
                     apply NMS_RSLRefine.bind (refl _)
                     intro flowScanner
                     cases flowScanner with
                     | Break residual => exact refl _
                     | Continue value =>
                       apply NMS_RSLRefine.bind (children.reconstruct _ _ _)
                       intro reconstruction
                       apply NMS_RSLRefine.bind (refl _)
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
end NMS_Effect242Fold
