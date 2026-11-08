from pathlib import Path
E=Path(__file__).parent
s=Path('lean/FJv_Top.lean').read_text()
ret=s.split('    let P :=',1)[1].split('\n := by',1)[0]
ret='    let P :='+ret
ret=ret.replace('FJv_Result.Outcome','FJv_DResult.Outcome')
# All names in the copied proposition are explicit local aliases at the host.
head='''import NNH_HostCtx
import RPx_Deployed
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_HostClaims
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open S2W_ReturnedCheckpoint S2W_CommittedCheckpoint S2W_WrapperLaws
open S2W_D189Consolidation S2W_NativeConsolidation S2W_TrustedStd
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open NNH_HostCtx FS FS2 MultiproofConeCanonical
open S2W_AuthenticatedInputs S2W_InputSchedule S2W_ExpandedChildren S2W_TraceSplice S2W_EntryWriteHistory
variable {W Tx : Type}
variable (L : Library W (Nat → Record))
variable (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))

def conclusion (ctx : Ctx W Tx) (native1 : S2W_ExtractionBoundary.First)
 (native2 : S2W_ExtractionBoundary.Second) : Prop :=
 let c := base ctx
 let indexError := ctx.fixed.indexError
 let reservation := ctx.fixed.reservation
 let allocator := NNE_AbortIndicator.allocator
 let e1 := ctx.i.entry
 let e2 := ctx.j.entry
 let w1 := ctx.world.w1
 let w2 := ctx.world.w2
 let data1 := ctx.i.data
 let data2 := ctx.j.data
 let slot := ctx.j.slot
 let saved := ctx.world.saved
 let post1 := writeBracket ctx.i.entry.heap 2 0 0 (source (nativeBytes ctx.world.saved))
 let post2 := ctx.j.entry.heap
 let hashv := hashv ctx
 let H := ctx.sha256
 let prior := ctx.fixed.prior
 let p := ctx.world.p
 let t := ctx.world.t
 let u := ctx.world.u
 let D := ctx.fixed.D
 let a := NNH_StateNormalize.normalize ctx.fixed.a
 let Q0 := ctx.fixed.Q0
 let Q1 := ctx.fixed.Q1
'''
# Native Outcome's boundary argument uses the deployed configuration boundary.
ret=ret.replace('(FIp_Install.boundaries c.boundaries)', '(FIp_Install.boundaries c.boundaries)')
(E/'NNH_HostClaims.lean').write_text(head+ret+'\n#print axioms conclusion\nend AspisR1.NNH_HostClaims\nend\n')
