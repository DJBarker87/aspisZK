import NJG_CarrierBack
set_option autoImplicit false
namespace AspisR1.NJG_PublicBack
open Aeneas Aeneas.Std Result NJG_InputCarriers

theorem withdrawal (p : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1WithdrawalPublicV1) :
 upWithdrawal (downWithdrawal p)=p := by cases p;rfl

theorem transfer (p : AspisR1PublicPreparation.pool_v1.payment_relation.PoolV1PrivateTransferPublicV1) :
 upTransfer (downTransfer p)=p := by cases p;rfl

theorem live (p : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLiveSnapshotV1) :
 upLive (downLive p)=p := by cases p;rfl

theorem after (p : AspisR1PublicPreparation.pool_v1.pair_terminal.PoolV1PairVerifiedAfterstateV1) :
 upAfter (downAfter p)=p := by cases p;rfl

theorem late (p : AspisR1PublicPreparation.pool_v1.pair_tree_profile.PoolV1PairLatePublicStatementV1) :
 upLate (downLate p)=p := by cases p;simp only [upLate,downLate,live,after]

theorem full (p : MP) : upPublic (downPublic p)=p := by
 cases p <;> simp only [upPublic,downPublic,transfer,withdrawal,late]

#print axioms withdrawal
#print axioms transfer
#print axioms live
#print axioms after
#print axioms late
#print axioms full
end AspisR1.NJG_PublicBack
