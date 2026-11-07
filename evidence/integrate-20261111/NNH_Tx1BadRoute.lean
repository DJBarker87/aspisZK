import NNH_Tx1RouteReject
import NNH_MAccountCarrier
import NNH_Libraries
set_option autoImplicit false
noncomputable section
namespace NNH_Tx1BadRoute
open Aeneas Aeneas.Std AspisR1 AdapterRw NND_Carrier NNH_ModelCarrier

theorem source (missing : IDa_Deployed.Uninstalled NFN_NEW_GeometryDictionary.CE)
 (env : RSL.Env) (err : NFN_NEW_GeometryDictionary.CE) (reserve : NP6_StdModel.Reservation)
 (program : solana_pubkey.Pubkey) (xs : Slice r1_pool_adapter.owned.OwnedAccount) (data : Slice U8)
 (bad : RSL.TX1_345.badRoute ⟨key program,accounts xs,bytes data⟩=true) :
 r1_pool_adapter.owned.stage1_owned (NNH_CorrectConfiguration.sdk missing env err reserve) program xs data=
 .ok (.Err solana_program_error.ProgramError.InvalidInstructionData) := by
 have compare0 := NNH_Tx1RouteCompare.source missing env err reserve data 10#u8
 have compare1 := NNH_Tx1RouteCompare.source missing env err reserve data 11#u8
 have byte10 : byte 10#u8=10 := by with_unfolding_all rfl
 have byte11 : byte 11#u8=11 := by with_unfolding_all rfl
 rw [byte10] at compare0
 rw [byte11] at compare1
 have size_eq : Slice.len xs=3#usize ↔ (accounts xs).length=3 := by
  constructor
  · intro eq
    have same := congrArg UScalar.val eq
    change xs.val.length=3 at same
    simpa only [accounts,List.length_map] using same
  · intro eq
    apply UScalar.eq_of_val_eq
    change xs.val.length=3
    simpa only [accounts,List.length_map] using eq
 have sizes : (Slice.len xs != 3#usize)=((accounts xs).length != 3) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne]
  exact not_congr size_eq
 have cmp0 : decide (bytes data=[3,10])=(bytes data==[3,10]) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,beq_iff_eq]
 have cmp1 : decide (bytes data=[3,11])=(bytes data==[3,11]) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,beq_iff_eq]
 apply NNH_Tx1RouteReject.source _ program xs data _ _ compare0 compare1
 rw [cmp0,cmp1,sizes]
 simpa only [RSL.TX1_345.badRoute,Bool.not_or] using bad
#print axioms source
end NNH_Tx1BadRoute
