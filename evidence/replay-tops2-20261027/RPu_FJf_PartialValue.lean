import RPu_FJf_PartialStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PartialValue
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ NE)
open FJf_PartialStep

theorem loop (f : Slice U8) (common : Array NQ 16#usize) (s : Usize)
    (hs : s.val < 4) (hc : FJf_QMArray.canon common)
    (iter : FIo_RangeNext.Range) (dot : FIo_Native.fast_pairing.EbyKDot) (out : NativeResult)
    (inv : Inv f common s (iter,dot))
    (run : FIo_Native.weights.partial_dot_loop iter f common s dot=ok out) : Post f common s out := by
  exact FIo_LoopInvariant.preserve
    (fun t : State => FIo_Native.weights.partial_dot_loop.body f common s t.1 t.2)
    (Inv f common s) (Post f common s) measure
    (fun t h r hr => by cases r <;> exact step f common s hs hc t h _ hr)
    (iter,dot) out inv run

theorem sixteen (f : Slice U8) (common : Array NQ 16#usize) (s : Usize)
    (hs : s.val < 4) (hc : FJf_QMArray.canon common) (out : NE)
    (run : FIo_Native.weights.partial_dot f common s=ok (.Ok out)) :
    FIo_WideValues.Canon out ∧ AspisR1CurrentWide.Proof.decodeWide (FIo_FieldBridge.wide out)=
      FJf_PartialCell.sumPrefix f common s 16 := by
  unfold FIo_Native.weights.partial_dot at run
  obtain ⟨dot,hd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨count,bound,model⟩ := FJf_EbyKNew.value dot hd
  refine loop f common s hs hc {start:=0#usize,«end»:=16#usize} dot (.Ok out) ?_ run
  refine ⟨rfl,by change (0:Nat)≤16;decide,?_,bound,?_⟩
  · simpa only [show (0#usize).val=0 from by decide] using count
  · simpa only [show (0#usize).val=0 from by decide,FJf_PartialCell.sumPrefix] using model
#print axioms loop
#print axioms sixteen
end AspisR1.FJf_PartialValue
end
