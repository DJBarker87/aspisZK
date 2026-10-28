import R1Z.PV_RunJoin_SourceZero20
import R1Z.PV_RunJoin_SourceNode0420
import R1Z.PV_RunJoin_SourceNodes0520
import R1Z.PV_RunJoin_SourceNodes0920
import R1Z.PV_RunJoin_SourceNodes1320
import R1Z.PV_RunJoin_SourceNodes1720
import R1Z.PV_RunJoin_SourceNodes2120
import R1Z.PV_RunJoin_SourceNodes5420
import R1Z.PV_RunJoin_SourceNodes3420
import R1Z.PV_RunJoin_SourceNodes3820
import R1Z.PV_RunJoin_SourceNodes4220
import R1Z.PV_RunJoin_SourceNodes4620
import R1Z.PV_RunJoin_SourceNodes5020
import R1Z.PV_RunJoin_SourceSponge0020
import R1Z.PV_RunJoin_SourceSponge0120
import R1Z.PV_RunJoin_SourceSponge0220
import R1Z.PV_RunJoin_SourceSponge0320
import R1Z.PV_RunJoin_SourceSponge2520
import R1Z.PV_RunJoin_SourceSponge2620
import R1Z.PV_RunJoin_SourceSponge2720
import R1Z.PV_RunJoin_SourceSponge2820
import R1Z.PV_RunJoin_SourceSponge2920
import R1Z.PV_RunJoin_SourceSponge3020
import R1Z.PV_RunJoin_SourceSponge3120
import R1Z.PV_RunJoin_SourceSponge3220
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_BankIdentification20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open PV_RunJoin_ReferenceFixtureResults
open BuilderForestAdmissionPort.pool_v1 BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
local instance : BuilderForestAdmissionPort.ExternalLinear := PV_Src_ExternalReference.dictionary
theorem transfer_blocks (pt : Parts) (hp : parts transferWitness transferPublic = ok pt) :
    ∀ b, b < 57 → ∀ row, row < 16 → ∀ lane, lane < 16 →
      (pt.blocks.val[b]!).val[row*16+lane]! =
        ((PV_RunJoin_FixtureBanks19.certificate false b).row row).val[lane]! := by
  intro b hb
  interval_cases b
  · exact PV_RunJoin_SourceSponge0020.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge0120.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge0220.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge0320.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode0420.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode0520.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode0620.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode0720.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode0820.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode0920.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1020.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1120.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1220.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1320.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1420.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1520.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1620.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1720.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1820.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode1920.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode2020.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode2120.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode2220.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode2320.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode2420.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge2520.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge2620.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge2720.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge2820.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge2920.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge3020.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge3120.transfer.rows pt hp
  · exact PV_RunJoin_SourceSponge3220.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode3320.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode3420.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode3520.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode3620.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode3720.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode3820.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode3920.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4020.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4120.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4220.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4320.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4420.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4520.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4620.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4720.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4820.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode4920.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode5020.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode5120.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode5220.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode5320.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode5420.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode5520.transfer.rows pt hp
  · exact PV_RunJoin_SourceNode5620.transfer.rows pt hp
#print axioms transfer_blocks
theorem transfer : pair_forest_trace.validate_forest_poseidon_rows PV_RunJoin_SourceBanks19.transferBank = ok (.Ok ()) := by
  obtain ⟨pt,hp⟩ := PV_RunJoin_PartsTotal19.transfer
  exact PV_RunJoin_SourceBankValidation19.transfer pt hp (PV_RunJoin_PartsCells19.tail pt)
    (PV_RunJoin_PartsCells19.cells pt false (transfer_blocks pt hp))
#print axioms transfer
theorem withdrawal_blocks (pt : Parts) (hp : parts withdrawalWitness withdrawalPublic = ok pt) :
    ∀ b, b < 57 → ∀ row, row < 16 → ∀ lane, lane < 16 →
      (pt.blocks.val[b]!).val[row*16+lane]! =
        ((PV_RunJoin_FixtureBanks19.certificate true b).row row).val[lane]! := by
  intro b hb
  interval_cases b
  · exact PV_RunJoin_SourceSponge0020.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceSponge0120.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceSponge0220.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceSponge0320.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode0420.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode0520.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode0620.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode0720.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode0820.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode0920.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1020.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1120.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1220.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1320.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1420.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1520.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1620.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1720.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1820.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode1920.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode2020.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode2120.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode2220.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode2320.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode2420.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceSponge2520.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceSponge2620.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceZero20.block27 pt hp
  · exact PV_RunJoin_SourceZero20.block28 pt hp
  · exact PV_RunJoin_SourceZero20.block29 pt hp
  · exact PV_RunJoin_SourceSponge3020.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceSponge3120.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceSponge3220.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode3320.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode3420.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode3520.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode3620.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode3720.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode3820.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode3920.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4020.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4120.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4220.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4320.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4420.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4520.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4620.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4720.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4820.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode4920.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode5020.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode5120.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode5220.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode5320.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode5420.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode5520.withdrawal.rows pt hp
  · exact PV_RunJoin_SourceNode5620.withdrawal.rows pt hp
#print axioms withdrawal_blocks
theorem withdrawal : pair_forest_trace.validate_forest_poseidon_rows PV_RunJoin_SourceBanks19.withdrawalBank = ok (.Ok ()) := by
  obtain ⟨pt,hp⟩ := PV_RunJoin_PartsTotal19.withdrawal
  exact PV_RunJoin_SourceBankValidation19.withdrawal pt hp (PV_RunJoin_PartsCells19.tail pt)
    (PV_RunJoin_PartsCells19.cells pt true (withdrawal_blocks pt hp))
#print axioms withdrawal
end R1Z.PV_RunJoin_BankIdentification20
