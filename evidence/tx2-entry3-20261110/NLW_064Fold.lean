import NLW_064Common
set_option autoImplicit false
noncomputable section
namespace NLW_064Fold
open Aeneas Aeneas.Std Result VTop_Stages AspisR1
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep NLW_064Invocation NLW_064Reference
/-- Exact outer chronology; the nested common record contains every entered
child's allocator/ABI/owned/effect data, including the first abort prefix. -/
def chronology {Ambient : Type} (H : Bytes → State) (s : Frame Ambient)
 (result : Result Reply) (records : Records H) : List (Event Ambient H) :=
 let p:=NLE_ParseInstall.parse s.args.proof
 match p with
 | .ok (.Ok _) => [.parse s p,.marker s,.common s result records]
 | _ => [.parse s p]
/-- Parameterized parent fold over the FULL sibling RowSpec. This is never a
row root: 065 is ungated, Root0/public clauses still need caller producers,
and the physical Frame/cut interpretation remains a reviewed item. -/
theorem parameterized {Ambient : Type} (H : Bytes → State) (bridge : ChildBridge H)
 (s : Frame Ambient) (publicBound : s.args.publicBytes.val.length≤1880)
 (root0 : NLW_Root0.Binds s.args.checkpoint s.args.proof)
 (result : Result Reply) (records : Records H) (events : List (Event Ambient H))
 (native : Invocation H s result records events) :
 result=transcription H s.args records ∧
 events=chronology H s result records ∧
 ChildFactsAtEntry H s.args result records := by
 cases native with
 | fail e parsed =>
   simp [transcription,chronology,ChildFactsAtEntry,parsed]
 | div parsed =>
   simp [transcription,chronology,ChildFactsAtEntry,parsed]
 | reject e parsed =>
   simp [transcription,chronology,ChildFactsAtEntry,parsed]
 | common v parsed result records child =>
   have facts:=NLW_064Common.install H bridge s.args publicBound root0 v parsed result records child
   refine ⟨?_,?_,?_⟩
   · simpa only [transcription,parsed] using facts.1
   · simp only [chronology,parsed]
   · simpa only [ChildFactsAtEntry,parsed] using facts
/-- No invalid decoder suffix is silently discarded at the common cut. -/
theorem no_invalid (H : Bytes → State) (bridge : ChildBridge H) (a : Args)
 (publicBound : a.publicBytes.val.length≤1880) (root0 : NLW_Root0.Binds a.checkpoint a.proof)
 (v : transport.Variant) (parsed : NLE_ParseInstall.parse a.proof=.ok (.Ok v))
 (records : Records H) : ¬NLT_NativeInvocation.Invalid H (NLT_RuntimeDigest.digest H) ()
 (childCode H a) records := by
 have packet:=bridge a.publicBytes a.proof a.checkpoint
  (NLE_ParseInstall.success a.proof v parsed).2 publicBound
  ((NLW_RowSpec_065.root0_same _ _).mp root0)
 exact packet.2 records
set_option pp.proofs false
#print parameterized
#print no_invalid
#print ChildBridge
#print NLW_RowSpec_065.RowSpec_065
#print NLT_Root.RowSpec
#print NLT_Root.CallLaw
#print Invocation
#print NLT_NativeInvocation.Invocation
#print NLT_NativeInvocation.Invalid
#print axioms parameterized
#print axioms no_invalid
end NLW_064Fold
