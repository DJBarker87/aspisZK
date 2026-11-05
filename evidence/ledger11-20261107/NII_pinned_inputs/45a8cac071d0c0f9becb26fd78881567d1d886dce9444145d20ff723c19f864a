import NHB_Domains
set_option autoImplicit false
namespace AspisR1.NHB_Canonical
open Aeneas Aeneas.Std Result
open Query31ExplicitScanBody

def State (s : NGQ_SamplerTrace.State) : Prop :=
  ∀ w∈s.accepted.val, w.val<262144

theorem set_preserves (xs : List U32) (i : Nat) (x : U32)
    (initial : ∀ w∈xs,w.val<262144) (value : x.val<262144) :
    ∀ w∈xs.set i x,w.val<262144 := by
  revert initial
  induction xs generalizing i with
  | nil => simp
  | cons y ys ih =>
    intro initial
    cases i with
    | zero =>
      intro w hw
      change w∈x::ys at hw
      rcases List.mem_cons.mp hw with h | h
      · simpa only [h] using value
      · exact initial w (List.mem_cons_of_mem y h)
    | succ i =>
      intro w hw
      change w∈y::ys.set i x at hw
      rcases List.mem_cons.mp hw with h | h
      · simpa only [h] using initial y (List.mem_cons_self ..)
      · exact ih i (fun z hz => initial z (List.mem_cons_of_mem y hz)) w h

theorem frame_preserves (s next : NGQ_SamplerTrace.State) (x : U32) (member : Bool)
    (frame : NGQ_SamplerStep.Frame s next x member)
    (initial : State s) (value : x.val<262144) : State next := by
  have array := frame.2.2
  unfold State
  cases member with
  | true =>
    simp only [if_true] at array
    rw [array]
    exact initial
  | false =>
    simp only [Bool.false_eq_true,if_false] at array
    rw [array]
    exact set_preserves s.accepted.val s.accepted_len.val x initial value

theorem initial : State NGQ_SamplerPacket.initial := by
  change ∀ w∈List.replicate 22 (0#u32),w.val<262144
  intro w hw
  have h : w=0#u32 := (List.mem_replicate.mp hw).2
  subst w
  decide

theorem word_invariant {cursor last : Nat} {xs : List U32}
    {s final : NGQ_SamplerTrace.State} {stop : Option Bool}
    (edges : NHB_WordTrace.Trace cursor xs s final last stop)
    (initial : State s) (words : ∀ w∈xs,w.val<262144) : State final := by
  revert initial words
  induction edges with
  | exhausted cursor s => intro initial _; exact initial
  | stopped cursor x xs s full => intro initial _; exact initial
  | continuing cursor x xs s next final last stop hlen hdraw frame tail ih =>
    intro initial words
    exact ih (frame_preserves s next x _ frame initial (words x (List.mem_cons_self ..)))
      (fun w hw => words w (List.mem_cons_of_mem x hw))

theorem mask_bound (x : U32) :
    (AspisR1QueryScanUnrolled.r0_transcript.queryMaskWord x).val<262144 := by
  change (x &&& 262143#u32).val<262144
  rw [UScalar.val_and]
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

theorem decoded (block : NGQ_SamplerDriver.Bytes32) (words : Array U32 8#usize)
    (call : Query31ConcreteWordsDriverChain.actualQueryWords block=ok words) :
    ∀ w∈words.val,w.val<262144 := by
  obtain ⟨ws,source,meaning⟩ := NGQ_SamplerWords.source block
  have same : ws=words := Result.ok.inj (source.symm.trans call)
  subst ws
  intro w hw
  rw [meaning] at hw
  obtain ⟨j,_,eq⟩ := List.mem_map.mp hw
  subst w
  exact mask_bound _

#print axioms mask_bound
#print axioms decoded
#print axioms set_preserves
#print axioms frame_preserves
#print axioms initial
#print axioms word_invariant
end AspisR1.NHB_Canonical
