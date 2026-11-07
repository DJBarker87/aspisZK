import NMN_OracleFold
set_option autoImplicit false
noncomputable section
namespace NMN_064
open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NLW_Full064
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
/-- Exact native allocation class, all predicates on064's own input slices.
The caller must supply getter/encoder facts; no child success is assumed. -/
structure Domain {X : Type} (a : Args X) : Prop where
 proofExtent : a.proof.val.length=57607
 checkpointExtent : a.checkpoint.val.length=1768
 publicBound : a.publicBytes.val.length≤1880
 root0 : NLP_InputDomain.Root0 a.checkpoint a.proof
/-- The actual CLOSED emitted parser at this recorded input. Its adopted
parser equality is derived below, not stored as a successful-child premise. -/
def ParserNative (proof : Slice U8) (reply : NMN_OracleFold.ParserReply) : Prop :=
 reply = NJS_Parse.map NLE_ParseInstall.reply (NJS_Parse.map NJS_Parse.reply
  (NJS_Extract.verifier.candidate.parse_shape
   Op3I_Std.ops.sliceNe Op3I_Std.ops.sliceEq Op3I_Std.ops.iterAny proof))
/-- Reviewed native G relation certified by NMN cuts under(bl). ChildNative
is an entered execution at precisely the recorded arguments, not its law.
The parent has no writes/events between calls; stopped End has prefix only. -/
inductive Native {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X) :
 End H s.args → List (Event Ambient X) → Prop where
 | observed (parsed : NMN_OracleFold.ParserReply)
   (common : transport.Variant → NLT_CompleteRoot.End H s.args.digest s.args.hash)
   (parser : ParserNative s.args.proof parsed)
   (child : ∀ v, parsed=.ok (.Ok v) → NLT_CompleteRoot.Native H s.args.digest
     s.args.publicBytes s.args.proof s.args.checkpoint s.args.hash (common v)) :
   Native H s (NMN_OracleFold.run H s parsed common).1 (NMN_OracleFold.run H s parsed common).2

def RowSpec {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X) : Prop :=
 (∀ outcome events,Native H s outcome events →
  Law H s.args outcome ∧ events=chronology H s outcome) ∧
 (∀ v,NLE_ParseInstall.parse s.args.proof=.ok (.Ok v) →
  ∀ records,¬NLT_NativeInvocation.Invalid H s.args.digest s.args.hash
   (NLT_NativeSource.skeleton H s.args.digest s.args.publicBytes s.args.proof
    s.args.checkpoint s.args.hash) records)

theorem parser {proof : Slice U8} {reply : NMN_OracleFold.ParserReply}
 (native : ParserNative proof reply) : reply=NLE_ParseInstall.parse proof :=
 native.trans (NLE_ParseInstall.emitted proof).symm
/-- Candidate semantic root. Native certificate/gate status is recorded in
NMN_CLOSED.json; this theorem alone does not confer ledger credit. -/
theorem root {Ambient X : Type} (H : Bytes → State) (s : Frame Ambient X)
 (domain : Domain s.args) : RowSpec H s := by
 have own : NMK_Domain.Caller s.args := ⟨domain.publicBound,domain.root0⟩
 constructor
 · intro outcome events native
   cases native with
   | observed parsed common parsedNative child =>
    exact NMN_OracleFold.composed H s own parsed common (parser parsedNative) child
 · intro v parsed records
   exact (NMK_Domain.child H s.args own v parsed).2 records
#print Domain
#print ParserNative
#print Native
#print RowSpec
#print parser
#print root
#print axioms parser
#print axioms root
end NMN_064
