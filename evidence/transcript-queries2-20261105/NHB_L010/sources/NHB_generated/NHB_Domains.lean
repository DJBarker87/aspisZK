import NHB_Sampler
set_option autoImplicit false
namespace AspisR1.NHB_Domains
open Aeneas Aeneas.Std Result
open Query31ExplicitListLoop Query31ExplicitScanBody

theorem word_invariant {cursor last : Nat} {xs : List U32}
    {s final : NGQ_SamplerTrace.State} {stop : Option Bool}
    (edges : NHB_WordTrace.Trace cursor xs s final last stop)
    (initial : validState s) : validState final := by
  revert initial
  induction edges with
  | exhausted cursor s => intro initial; exact initial
  | stopped cursor x xs s full => intro initial; exact initial
  | continuing cursor x xs s next final last stop hlen hdraw frame tail ih =>
    intro _
    exact ih (NGQ_SamplerStep.valid hlen hdraw frame)

/-- This is the native next-block caller domain, derived from local frames.
No assumption that the scan returned a successful sampler output is needed. -/
theorem block_invariant (block : NGQ_SamplerDriver.Bytes32)
    (words : Array U32 8#usize) (s final : NGQ_SamplerTrace.State)
    (last : Nat) (pending : Option Bool)
    (decode : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words)
    (edges : NHB_WordTrace.Trace 0 words.val s final last pending)
    (initial : validState s) :
    NGQ_SamplerPacket.Scan s block=ok (optionStop pending,final) ∧
      validState final ∧ last≤8 := by
  obtain ⟨call,bound⟩ := NHB_BlockTrace.block_source block words s final last pending decode edges
  exact ⟨call,word_invariant edges initial,bound⟩

#print axioms word_invariant
#print axioms block_invariant
end AspisR1.NHB_Domains
