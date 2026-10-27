import RPv_FJg_HighStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_HighValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
open FJg_HighStep

theorem loop (f : Array NE 4#usize) (common : Array NQ 4#usize)
    (hf : FIo_ArrayCanon.Holds f) (hc : FJf_QMArray.canon common)
    (iter : FIo_RangeNext.Range) (dot : FIo_Native.fast_pairing.EbyKDot) (out : NativeResult)
    (inv : Inv f common (iter,dot))
    (run : FIo_Native.weights.high_dot_loop iter f common dot=ok out) : Post f common out := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIo_Native.weights.high_dot_loop.body f common t.1 t.2)
    (Inv f common) (Post f common) measure
    (fun t h r hr => by cases r <;> exact step f common hf hc t h _ hr)
    (iter,dot) out inv run

theorem four (f : Array NE 4#usize) (common : Array NQ 4#usize)
    (hf : FIo_ArrayCanon.Holds f) (hc : FJf_QMArray.canon common) (out : NE)
    (run : FIo_Native.weights.high_dot f common=ok (.Ok out)) :
    FIo_WideValues.Canon out ∧ AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide out)=
      FJg_HighCell.sumPrefix f common 4 := by
  unfold FIo_Native.weights.high_dot at run
  obtain ⟨dot,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨count,bound,model⟩ := FJf_EbyKNew.value dot hd
  refine loop f common hf hc {start:=0#usize,«end»:=4#usize} dot (.Ok out) ?_ run
  refine ⟨rfl,by change (0:Nat)≤4;decide,?_,bound,?_⟩
  · simpa only [show (0#usize).val=0 from by decide] using count
  · simpa only [show (0#usize).val=0 from by decide,FJg_HighCell.sumPrefix] using model
#print axioms loop
#print axioms four
end AspisR1.FJg_HighValue
end
