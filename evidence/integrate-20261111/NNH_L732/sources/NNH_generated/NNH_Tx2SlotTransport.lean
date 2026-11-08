import NNH_CommonSlots
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Tx2SlotTransport
open Aeneas Aeneas.Std Result VTop_Stages
variable (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
abbrev stage := DrvC_Installation.stage (NNH_CorrectConfiguration.configuration missing env err reserve)

theorem geometry (q : Array U32 22#usize) (start finish : Usize) :
 (stage missing env err reserve).op11 q start finish = NJC_ClosedCalls.geometry q start finish := by
 rw [NJC_ClosedCalls.geometry_clause]
 rfl

theorem finish (v : verifier.View) (p : verifier.Prepared) (a : verifier.Accumulator) :
 (stage missing env err reserve).op19 v p a none = NLB_Parent.finish reserve v p a none := by
 rfl
#print axioms geometry
#print axioms finish
#print Port5Q1_GeometryTerminal.install
#print AspisR1.NLB_CommonTransport.common_transport
#check NHT_QueryTail.source
#print NID_ResumeCanonical.ECanonical
end AspisR1.NNH_Tx2SlotTransport
end
