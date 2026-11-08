import NNH_Tx2SlotTransport
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_Tx2LiteralSlots
open Aeneas Aeneas.Std Result VTop_Stages NNH_Tx2SlotTransport
variable (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (r : NP6_StdModel.Reservation)

theorem pending (bs : Slice aspis_core.field.QM31) :
 (stage missing env err r).op10 bs = Port3_NativePendingInstall.source env.reservation bs := rfl

theorem flush (p : verifier.BatchedWeights) (bs : Slice aspis_core.field.QM31) :
 (stage missing env err r).op9 p bs = Port3_FlushInstall.flush p bs := rfl

theorem mark (obs : Option (verifier.Phase → Result Unit)) (phase : verifier.Phase) :
 (stage missing env err r).op13 obs phase = NHV_ReleaseOps.mark obs phase := rfl

theorem powers (n : Usize) (g : aspis_core.field.wide_exact.WideExact) :
 (stage missing env err r).op17 n g = Tx2N_Powers.powers n g := rfl

theorem constants :
 (stage missing env err r).op14 = NHT_Constants.compact.OFF_ROUND1 ∧
 (stage missing env err r).op15 = NHT_Constants.compact.OFF_FOLDED_ROOT ∧
 (stage missing env err r).op16 = .ok 10#usize ∧
 (stage missing env err r).op20 = NHT_Constants.compact.OFF_OPENINGS ∧
 (stage missing env err r).op21 = NHT_Constants.compact.OFF_FINAL ∧
 (stage missing env err r).op22 = NHT_Constants.compact.OFF_ROUND0 ∧
 (stage missing env err r).op23 = NHT_Constants.compact.OFF_INACTIVE := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
 · with_unfolding_all rfl
 · with_unfolding_all rfl

#print Port1_LibrarySource.decode
#print NHV_InactivePacket.emitted
#print axioms pending
#print axioms flush
#print axioms mark
#print axioms powers
#print axioms constants
end AspisR1.NNH_Tx2LiteralSlots
end
