import PFin_Attach
import PFin_BoundCaller
import PFin_Caller
import PFin_Cont
import PFin_Digest
import PFin_Endpoint
import PFin_Entry
import PFin_Final
import PFin_FinalResult
import PFin_Finish
import PFin_Gates
import PFin_Packet
import PFin_Prepared
import PFin_Result
import PFin_SelectedPair
import PFin_SelectedResult
import PFin_Ten
import PFin_Top

set_option pp.deepTerms true
set_option pp.fullNames true
set_option format.width 160
#print AspisR1.Rc2_Top.deployed
#print AspisR1.PFin_Top.deployed
#print AspisR1.Rc2_Result.Outcome
#print AspisR1.PFin_FinalResult.Outcome
#print AspisR1.T2R_CallerSource.Outcome
#print AspisR1.PFin_BoundCaller.Outcome
#print AspisR1.T2R_ContSource.Outcome
#print AspisR1.PFin_Cont.Outcome
#print AspisR1.T2R_Ten.Outcome
#print AspisR1.PFin_Ten.Outcome
#print AspisR1.T2R_Finish.Outcome
#print AspisR1.PFin_Finish.Outcome
#print AspisR1.Tx1Q_Endpoint.WhenBound
#print AspisR1.PFin_Endpoint.Outcome
#print AspisR1.PFin_Packet.Facts
#print axioms AspisR1.PFin_Attach.from_cut
#print axioms AspisR1.PFin_BoundCaller.from_cut
#print axioms AspisR1.PFin_Cont.same_parsed
#print axioms AspisR1.PFin_Cont.from_cut
#print axioms AspisR1.PFin_Digest.same
#print axioms AspisR1.PFin_Digest.prepared
#print axioms AspisR1.PFin_Endpoint.consume
#print axioms AspisR1.PFin_Entry.from_cut
#print axioms AspisR1.PFin_Final.accepted
#print axioms AspisR1.PFin_Finish.consume
#print axioms AspisR1.PFin_Gates.decoded
#print axioms AspisR1.PFin_Gates.closed
#print axioms AspisR1.PFin_Packet.from_cut
#print axioms AspisR1.PFin_Prepared.from_cut
#print axioms AspisR1.PFin_Result.strengthen
#print axioms AspisR1.PFin_SelectedPair.accepted
#print axioms AspisR1.PFin_Ten.consume
#print axioms AspisR1.PFin_Top.deployed
