import NHS_QueryPacket
import NFW_Invert
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHS_QueryBounds
open Aeneas Aeneas.Std Result
open NGQ_SamplerDriver

def Bounded : Out → Prop
 | .Ok (q,_) => ∀ w∈q.val,w.val<262144
 | .Err _ => True

theorem finish (advances : Blocks) (index : Usize) (s : State) (out : Out)
 (canonical : NHB_Canonical.State s)
 (call : AspisR1Query31Transcript.finishAdvance advances index s=ok out) : Bounded out := by
 unfold AspisR1Query31Transcript.finishAdvance at call
 obtain ⟨reply,finished,call⟩ := NFW_Invert.bind _ _ _ call
 cases reply with
 | Err e =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
     core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
     core.convert.FromSame] at call
   cases Result.ok.inj call
   trivial
 | Ok q =>
   have same := (AspisR1Query31Transcript.finish_success_iff s q).mp finished
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at call
   obtain ⟨next,_,last⟩ := NFW_Invert.bind _ _ _ call
   cases Result.ok.inj last
   change ∀ w∈q.val,w.val<262144
   rw [same.2]
   exact canonical

/-- The22 bounds come from the SAME native word/block cuts and actual masked
words, with zero initialization. No successful independent query array. -/
theorem blocks {advances : Blocks} {inputs : List (Bytes32×Usize)} {s : State} {out : Out}
 (cuts : NHK_NativeBlocks.Cuts advances inputs s out)
 (canonical : NHB_Canonical.State s) : Bounded out := by
 induction cuts with
 | exhausted s out finished => exact finish advances _ s out canonical finished
 | stopped block index tail s next out words last pending decode edges stop finished =>
   have nextCanonical := NHB_Canonical.word_invariant (NHK_NativeWords.association edges)
     canonical (NHB_Canonical.decoded block words decode)
   exact finish advances index next out nextCanonical finished
 | continuing block index tail s next out words last pending decode edges stop rest ih =>
   exact ih (NHB_Canonical.word_invariant (NHK_NativeWords.association edges)
     canonical (NHB_Canonical.decoded block words decode))
#print axioms finish
#print axioms blocks
end AspisR1.NHS_QueryBounds
