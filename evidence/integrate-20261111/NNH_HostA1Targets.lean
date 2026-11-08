import NNH_HostHeadline
import NNH_HostExec
import NNH_HostOracle
import NNH_HostRecorderEvent
import NNH_HostSplit
import NNH_S1CodecStatus
import NNH_Stage1PrepareDomainR4
import NNH_HostClockFinding
import NNH_HostExec
import NNH_ReturnsBundle
import NNH_Tx1BadRoute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostA1Targets
open Aeneas Aeneas.Std Result S2W_D189Entry S2W_ReturnedCheckpoint
open NNH_HostCtx
/-- Unproved exact literal-host A1 value targets. They are not assumptions of
a claimed interface field. All stage1 occurrences, including trace invocations,
are quantified; only the Err *class* is required. -/
def ok : Prop := ∀ {W Tx : Type} (c : Ctx W Tx) (e : Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8),
 NNH_ReturnsBundle.tx1Value (NNE_PhysicalAccepted.child1 NND_Carrier.error e p data)
  (envOf c) = .ok (nativeBytes saved) →
 model1 c p e.first data = .ok (.Ok saved)

def err : Prop := ∀ {W Tx : Type} (c : Ctx W Tx) (e : Entry)
 (p : S2W_ExtractionBoundary.Program) (data : Slice U8) (error : RSL.ProgramError),
 NNH_ReturnsBundle.tx1Value (NNE_PhysicalAccepted.child1 NND_Carrier.error e p data)
  (envOf c) = .error error →
 ¬ ∃ saved, model1 c p e.first data = .ok (.Ok saved)

theorem bad_route {W Tx : Type} (c : Ctx W Tx)
 (p : S2W_ExtractionBoundary.Program) (e : Entry) (data : Slice U8)
 (bad : RSL.TX1_345.badRoute
  ⟨NND_Carrier.key p,NNH_ModelCarrier.accounts e.first,NND_Carrier.bytes data⟩ = true) :
 ¬ ∃ saved, model1 c p e.first data = .ok (.Ok saved) := by
 intro ⟨saved,accepted⟩
 have rejected := NNH_Tx1BadRoute.source NNH_HostSeed.m0 (envOf c) c.fixed.indexError
  c.fixed.reservation p e.first data bad
 change _root_.AdapterRw.r1_pool_adapter.owned.stage1_owned
  (NNH_CorrectConfiguration.sdk NNH_HostSeed.m0 (envOf c) c.fixed.indexError c.fixed.reservation)
  p e.first data = .ok (.Ok saved) at accepted
 rw [rejected] at accepted
 cases accepted
#print axioms ok
#print axioms err
#print axioms bad_route
end AspisR1.NNH_HostA1Targets
end

#print axioms AspisR1.NNH_LiteralHost.a0
#print axioms AspisR1.NNH_LiteralHost.r0
#print axioms AspisR1.NNH_HostHeadline.headline
#print axioms AspisR1.NNH_HostExec.exec
#print axioms AspisR1.NNH_HostExec.recSelect
#print axioms NNH_RecordSig.a3
#print axioms NNH_RecordSig.a4
#print axioms NNH_RecordSig.a5
#print axioms NNH_ReturnsBundle.tx1_returns
#print axioms NNH_Stage1PrepareDomainR4.decoder_discharge
