import R1Z.PV_RunJoin_TransferFrontier0021
import R1Z.PV_RunJoin_TransferFrontier0121
import R1Z.PV_RunJoin_TransferFrontier0221
import R1Z.PV_RunJoin_TransferFrontier0321
import R1Z.PV_RunJoin_TransferFrontier0421
import R1Z.PV_RunJoin_TransferFrontier0521
import R1Z.PV_RunJoin_TransferFrontier0621
import R1Z.PV_RunJoin_TransferFrontier0721
import R1Z.PV_RunJoin_TransferFrontier0821
import R1Z.PV_RunJoin_TransferFrontier0921
import R1Z.PV_RunJoin_TransferFrontier1021
import R1Z.PV_RunJoin_TransferFrontier1121
import R1Z.PV_RunJoin_TransferFrontier1221
import R1Z.PV_RunJoin_TransferFrontier1321
import R1Z.PV_RunJoin_TransferFrontier1421
import R1Z.PV_RunJoin_TransferFrontier1521
import R1Z.PV_RunJoin_TransferFrontier1621
import R1Z.PV_RunJoin_TransferFrontier1721
import R1Z.PV_RunJoin_TransferFrontier1821
import R1Z.PV_RunJoin_TransferFrontier1921
import R1Z.PV_RunJoin_WithdrawalFrontier0021
import R1Z.PV_RunJoin_WithdrawalFrontier0121
import R1Z.PV_RunJoin_WithdrawalFrontier0221
import R1Z.PV_RunJoin_WithdrawalFrontier0321
import R1Z.PV_RunJoin_WithdrawalFrontier0421
import R1Z.PV_RunJoin_WithdrawalFrontier0521
import R1Z.PV_RunJoin_WithdrawalFrontier0621
import R1Z.PV_RunJoin_WithdrawalFrontier0721
import R1Z.PV_RunJoin_WithdrawalFrontier0821
import R1Z.PV_RunJoin_WithdrawalFrontier0921
import R1Z.PV_RunJoin_WithdrawalFrontier1021
import R1Z.PV_RunJoin_WithdrawalFrontier1121
import R1Z.PV_RunJoin_WithdrawalFrontier1221
import R1Z.PV_RunJoin_WithdrawalFrontier1321
import R1Z.PV_RunJoin_WithdrawalFrontier1421
import R1Z.PV_RunJoin_WithdrawalFrontier1521
import R1Z.PV_RunJoin_WithdrawalFrontier1621
import R1Z.PV_RunJoin_WithdrawalFrontier1721
import R1Z.PV_RunJoin_WithdrawalFrontier1821
import R1Z.PV_RunJoin_WithdrawalFrontier1921
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PublicFrontier21
open R0Z.WriterRefine PV_RunJoin_FixtureRecords
theorem transfer : PV_RunJoin_PublicCore21.transfer.nextFrontier = (fixturePublic false).nextFrontier := by
  funext l
  fin_cases l
  · exact PV_RunJoin_TransferFrontier0021.source
  · exact PV_RunJoin_TransferFrontier0121.source
  · exact PV_RunJoin_TransferFrontier0221.source
  · exact PV_RunJoin_TransferFrontier0321.source
  · exact PV_RunJoin_TransferFrontier0421.source
  · exact PV_RunJoin_TransferFrontier0521.source
  · exact PV_RunJoin_TransferFrontier0621.source
  · exact PV_RunJoin_TransferFrontier0721.source
  · exact PV_RunJoin_TransferFrontier0821.source
  · exact PV_RunJoin_TransferFrontier0921.source
  · exact PV_RunJoin_TransferFrontier1021.source
  · exact PV_RunJoin_TransferFrontier1121.source
  · exact PV_RunJoin_TransferFrontier1221.source
  · exact PV_RunJoin_TransferFrontier1321.source
  · exact PV_RunJoin_TransferFrontier1421.source
  · exact PV_RunJoin_TransferFrontier1521.source
  · exact PV_RunJoin_TransferFrontier1621.source
  · exact PV_RunJoin_TransferFrontier1721.source
  · exact PV_RunJoin_TransferFrontier1821.source
  · exact PV_RunJoin_TransferFrontier1921.source
#print axioms transfer
theorem withdrawal : PV_RunJoin_PublicCore21.withdrawal.nextFrontier = (fixturePublic true).nextFrontier := by
  funext l
  fin_cases l
  · exact PV_RunJoin_WithdrawalFrontier0021.source
  · exact PV_RunJoin_WithdrawalFrontier0121.source
  · exact PV_RunJoin_WithdrawalFrontier0221.source
  · exact PV_RunJoin_WithdrawalFrontier0321.source
  · exact PV_RunJoin_WithdrawalFrontier0421.source
  · exact PV_RunJoin_WithdrawalFrontier0521.source
  · exact PV_RunJoin_WithdrawalFrontier0621.source
  · exact PV_RunJoin_WithdrawalFrontier0721.source
  · exact PV_RunJoin_WithdrawalFrontier0821.source
  · exact PV_RunJoin_WithdrawalFrontier0921.source
  · exact PV_RunJoin_WithdrawalFrontier1021.source
  · exact PV_RunJoin_WithdrawalFrontier1121.source
  · exact PV_RunJoin_WithdrawalFrontier1221.source
  · exact PV_RunJoin_WithdrawalFrontier1321.source
  · exact PV_RunJoin_WithdrawalFrontier1421.source
  · exact PV_RunJoin_WithdrawalFrontier1521.source
  · exact PV_RunJoin_WithdrawalFrontier1621.source
  · exact PV_RunJoin_WithdrawalFrontier1721.source
  · exact PV_RunJoin_WithdrawalFrontier1821.source
  · exact PV_RunJoin_WithdrawalFrontier1921.source
#print axioms withdrawal
end R1Z.PV_RunJoin_PublicFrontier21
