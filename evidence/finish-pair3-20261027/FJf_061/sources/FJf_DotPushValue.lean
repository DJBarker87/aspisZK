import FJf_DotLaneStep
set_option autoImplicit false
namespace AspisR1.FJf_DotPushValue
open Aeneas Aeneas.Std Result
open FJf_DotLane (Dot)
open FJf_DotLaneStep

theorem loop (base : Dot) (raw : Array U64 4#usize)
    (iter : FIo_RangeNext.Range) (dot out : Dot) (inv : Inv base raw (iter,dot))
    (run : FIo_Native.fast_pairing.canonical.Dot.push_loop iter dot raw=ok out) : Post base raw out := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIo_Native.fast_pairing.canonical.Dot.push_loop.body raw t.1 t.2)
    (Inv base raw) (Post base raw) measure
    (fun t h r hr => by cases r <;> exact step base raw t h _ hr)
    (iter,dot) out inv run

theorem four (raw : Array U64 4#usize) (dot out : Dot)
    (run : FIo_Native.fast_pairing.canonical.Dot.push_loop {start:=0#usize,«end»:=4#usize}
      dot raw=ok out) : Post dot raw out := by
  refine loop dot raw {start:=0#usize,«end»:=4#usize} dot out ?_ run
  refine ⟨rfl,?_,?_⟩
  · change (0:Nat)≤4
    decide
  · intro j hj
    dsimp only
    simp only [show (0#usize).val=0 from by decide,Nat.not_lt_zero,if_false]

theorem source (dot out : Dot) (a b : FIo_Native.fast_pairing.canonical.Q)
    (run : FIo_Native.fast_pairing.canonical.Dot.push dot a b=ok out) :
    ∃ raw,FIo_Native.fast_pairing.canonical.Q.raw a b=ok raw ∧ Post dot raw out := by
  unfold FIo_Native.fast_pairing.canonical.Dot.push at run
  obtain ⟨raw,hr,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  exact ⟨raw,hr,four raw dot out run⟩
#print axioms loop
#print axioms four
#print axioms source
end AspisR1.FJf_DotPushValue
