import NIY_ReaderFrames
set_option autoImplicit false
noncomputable section
namespace NIY_EarlyDomains
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

/-- Exact first-three source reader facts, on the SAME Fields witness derived
from the returned pair. Native source/caller installation is not assumed here. -/
theorem first3 (reserved : Bool) (ck : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (f : OraclePortCkptAbiSourceFields.Fields (CheckpointBytes4Ops.ops reserved) ck .S2 p a)
 (length : ck.val.length=1768) :
 f.rState.at.val=112 ∧ f.rState.bytes=ck ∧
 f.rRoot0.at.val=144 ∧ f.rRoot0.bytes=ck ∧
 f.rRoot1.at.val=176 ∧ f.rRoot1.bytes=ck := by
 obtain ⟨sat,sbytes⟩ := NIY_ReaderFrames.raw 32#usize ⟨ck,80#usize⟩ p.state f.rState
   (by change 80+32≤ck.val.length;omega) f.stateRead
 have sat' : f.rState.at.val=112 := by simpa using sat
 obtain ⟨rat0,rbytes0⟩ := NIY_ReaderFrames.raw 32#usize f.rState f.root0 f.rRoot0
   (by change f.rState.at.val+32≤f.rState.bytes.val.length;rw [sat',sbytes,length];omega) f.root0Read
 have rat0' : f.rRoot0.at.val=144 := by simpa [sat'] using rat0
 have rb0 : f.rRoot0.bytes=ck := rbytes0.trans sbytes
 obtain ⟨rat1,rbytes1⟩ := NIY_ReaderFrames.raw 32#usize f.rRoot0 f.root1 f.rRoot1
   (by change f.rRoot0.at.val+32≤f.rRoot0.bytes.val.length;rw [rat0',rb0,length];omega) f.root1Read
 have rat1' : f.rRoot1.at.val=176 := by simpa [rat0'] using rat1
 exact ⟨sat',sbytes,rat0',rb0,rat1',rbytes1.trans rb0⟩

/-- Derive the actual early E/E/E/E/K call domains and cursors independently
from their executed source reader facts. The length premise remains explicit. -/
theorem typed (reserved : Bool) (ck : Slice U8) (p : verifier.Prepared) (a : verifier.Accumulator)
 (f : OraclePortCkptAbiSourceFields.Fields (CheckpointBytes4Ops.ops reserved) ck .S2 p a)
 (length : ck.val.length=1768) :
 f.rGamma.at.val=208 ∧ f.rGamma.bytes=ck ∧
 f.rKappa.at.val=240 ∧ f.rKappa.bytes=ck ∧
 f.rAlpha0.at.val=272 ∧ f.rAlpha0.bytes=ck ∧
 f.rAlpha1.at.val=304 ∧ f.rAlpha1.bytes=ck ∧
 f.rRho.at.val=320 ∧ f.rRho.bytes=ck := by
 obtain ⟨_,_,_,_,rootAt,rootBytes⟩ := first3 reserved ck p a f length
 obtain ⟨ga,gb⟩ := NIY_ReaderFrames.e f.rRoot1 f.rGamma (.Ok p.gamma)
   (by rw [rootAt,rootBytes,length];omega) f.gammaRead
 have gb' : f.rGamma.bytes=ck := gb.trans rootBytes
 obtain ⟨ka,kb⟩ := NIY_ReaderFrames.e f.rGamma f.rKappa (.Ok p.kappa)
   (by rw [gb',length];omega) f.kappaRead
 have kb' : f.rKappa.bytes=ck := kb.trans gb'
 obtain ⟨a0a,a0b⟩ := NIY_ReaderFrames.e f.rKappa f.rAlpha0 (.Ok f.alpha0)
   (by rw [kb',length];omega) f.alpha0Read
 have a0b' : f.rAlpha0.bytes=ck := a0b.trans kb'
 obtain ⟨a1a,a1b⟩ := NIY_ReaderFrames.e f.rAlpha0 f.rAlpha1 (.Ok f.alpha1)
   (by rw [a0b',length];omega) f.alpha1Read
 have a1b' : f.rAlpha1.bytes=ck := a1b.trans a0b'
 obtain ⟨ra,rb⟩ := NID_ReadStepFrame.next f.rAlpha1 f.rRho (.Ok p.rho)
   (by rw [a1b',length];omega) f.rhoRead
 exact ⟨by omega,gb',by omega,kb',by omega,a0b',by omega,a1b',by omega,rb.trans a1b'⟩
#print axioms first3
#print axioms typed
end NIY_EarlyDomains
