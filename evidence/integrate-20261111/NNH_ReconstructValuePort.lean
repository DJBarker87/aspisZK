import NNH_PoolValuePorts
set_option autoImplicit false
noncomputable section
namespace NNH_ReconstructValuePort
open Aeneas Aeneas.Std AdapterRw

theorem ok (q : LIBB_PoolCarriers.Request) (a : LIBB_AuthCarrier.Raw)
 (after : LIBB_PoolCarriers.Afterstate) (statement : LIBB_PoolCarriers.Statement)
 (success : LIBB_PoolReconstruct.evaluator q (NND_Carrier.auth a) after=.ok statement) :
 AspisR1.NFY_JHf_ReconstructionSlot.source q a after=.ok (.Ok statement) := by
 unfold LIBB_PoolReconstruct.evaluator at success
 rw [LIBB_AuthCarrier.roundtrip] at success
 cases source : AspisR1.NFY_JHf_ReconstructionSlot.source q a after with
 | fail e => simp only [source,LIBB_ModelGraph.value,LIBB_PoolReconstruct.reply,NMS_R2N_RSLError.reply] at success; cases success
 | div => simp only [source,LIBB_ModelGraph.value,LIBB_PoolReconstruct.reply,NMS_R2N_RSLError.reply] at success; cases success
 | ok reply => cases reply with
   | Err e => simp only [source,LIBB_ModelGraph.value,LIBB_PoolReconstruct.reply,NMS_R2N_RSLError.reply] at success; cases success
   | Ok st =>
     simp only [source,LIBB_ModelGraph.value,LIBB_PoolReconstruct.reply,NMS_R2N_RSLError.reply,Except.ok.injEq,id_eq] at success
     cases success
     rfl
#print axioms ok
end NNH_ReconstructValuePort
