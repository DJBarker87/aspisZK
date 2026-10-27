import RPu_FJj_ByteDotStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_ByteDotLoop
open Aeneas Aeneas.Std Result
open FIo_FieldBridge (NQ)
open FJj_ByteDotStep

theorem value (f : Slice U8) (scratch : Slice NQ) (hc : FJj_QMSlice.canon scratch)
    (dot out : FIo_Native.fast_pairing.EbyKDot)
    (new : FIo_Native.fast_pairing.EbyKDot.new=ok dot)
    (run : FIo_Native.weights.push_byte_products dot f scratch 64#usize=ok (.Ok (),out)) :
    FJf_EbyKCodec.Bound out ∧ out.count.val=64 ∧
      FJf_EbyKCodec.model out=FJj_ByteDotCell.sumPrefix f scratch 64 := by
  obtain ⟨count,bound,model⟩ := FJf_EbyKNew.value dot new
  have inv : Inv f scratch ({start:=0#usize,«end»:=64#usize},dot) := by
    refine ⟨rfl,by change (0:Nat)≤64;omega,count,bound,?_⟩
    exact model
  exact FIo_LoopInvariant.preserve
    (fun t : State=>FIo_Native.weights.push_byte_products_loop.body f scratch t.1 t.2)
    (Inv f scratch) (Post f scratch) measure
    (fun t h r hr=>by cases r <;> exact step f scratch hc t h _ hr)
    ({start:=0#usize,«end»:=64#usize},dot) (.Ok (),out) inv run
#print axioms value
end AspisR1.FJj_ByteDotLoop
end
