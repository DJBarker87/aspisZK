import NLW_Full064Fold
set_option autoImplicit false
noncomputable section
namespace NMD_CutState
open Aeneas Aeneas.Std VTop_Stages AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Physical state is additional to the predecessor's logical World. A concrete
native certificate must interpret it; no heap/allocator decoder is assumed here. -/
structure Parent (Ambient X Physical : Type) where
 frame : Frame Ambient X
 physical : Physical
/-- Exact boundary records retain the entire original parent, not only spans.
The common child's effect is a separate full packet, never an empty modifies. -/
structure ParseBoundary (Ambient X Physical : Type) where
 before : Parent Ambient X Physical
 after : Parent Ambient X Physical
 reply : Result (core.result.Result transport.Variant verifier.Error)
structure CommonBoundary (Ambient X Physical : Type) where
 original : Parent Ambient X Physical
 entered : Parent Ambient X Physical
 postPhysical : Physical
/-- Obligations for the native producer. These propositions are not native
facts until the actual compiled-function contracts and controls establish them. -/
def ParseSegment {Ambient X Physical : Type}
 (b : ParseBoundary Ambient X Physical) : Prop :=
 b.after=b.before ∧ b.reply=NLE_ParseInstall.parse b.before.frame.args.proof

def CommonArguments {Ambient X Physical : Type}
 (b : CommonBoundary Ambient X Physical) : Prop := b.entered=b.original
/-- Full-record equality transports byte contents, backend identity and World;
no address/length-to-byte inference is used. -/
theorem exact_arguments {Ambient X Physical : Type}
 (b : CommonBoundary Ambient X Physical) (native : CommonArguments b) :
 b.entered.frame.args=b.original.frame.args ∧
 b.entered.frame.world=b.original.frame.world ∧
 b.entered.physical=b.original.physical := by
 cases b with
 | mk original entered post =>
  change entered=original at native
  subst entered
  exact ⟨rfl,rfl,rfl⟩
/-- The only internally discharged domain clause is obtained at parse success.
The public bound and Root0 are retained caller clauses, per ruling (bf). -/
theorem child_domain {Ambient X Physical : Type}
 (b : ParseBoundary Ambient X Physical) (native : ParseSegment b)
 (v : transport.Variant) (success : b.reply=.ok (.Ok v))
 (publicBound : b.before.frame.args.publicBytes.val.length≤1880)
 (root0 : NLW_Root0.Binds b.before.frame.args.checkpoint b.before.frame.args.proof) :
 b.after.frame.args.proof.val.length=57607 ∧
 b.after.frame.args.publicBytes.val.length≤1880 ∧
 NLP_InputDomain.Root0 b.after.frame.args.checkpoint b.after.frame.args.proof := by
 have parsed : NLE_ParseInstall.parse b.before.frame.args.proof=.ok (.Ok v) :=
  native.2.symm.trans success
 have length := (NLE_ParseInstall.success b.before.frame.args.proof v parsed).2
 rw [native.1]
 exact ⟨length,publicBound,(NLW_RowSpec_065.root0_same _ _).mp root0⟩
#print axioms exact_arguments
#print axioms child_domain
end NMD_CutState
