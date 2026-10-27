import FJj_ByteDotCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJj_ByteDotStep
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NQ)
abbrev State := FIo_RangeNext.Range × FIo_Native.fast_pairing.EbyKDot
abbrev NativeResult := core.result.Result Unit FIo_Native.verifier.Error × FIo_Native.fast_pairing.EbyKDot

def Inv (f : Slice U8) (scratch : Slice NQ) (t : State) : Prop :=
  t.1.end.val=64 ∧ t.1.start.val≤64 ∧ t.2.count.val=t.1.start.val ∧
  FJf_EbyKCodec.Bound t.2 ∧ FJf_EbyKCodec.model t.2=FJj_ByteDotCell.sumPrefix f scratch t.1.start.val

def Post (f : Slice U8) (scratch : Slice NQ) (r : NativeResult) : Prop :=
  match r.1 with
  | .Err _=>True
  | .Ok _=>FJf_EbyKCodec.Bound r.2 ∧ r.2.count.val=64 ∧
      FJf_EbyKCodec.model r.2=FJj_ByteDotCell.sumPrefix f scratch 64

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (f : Slice U8) (scratch : Slice NQ) (hc : FJj_QMSlice.canon scratch)
    (t : State) (inv : Inv f scratch t) (out : ControlFlow State NativeResult)
    (run : FIo_Native.weights.push_byte_products_loop.body f scratch t.1 t.2=ok out) :
    match out with
    | .done r=>Post f scratch r
    | .cont next=>Inv f scratch next ∧ measure next < measure t := by
  rcases t with ⟨iter,dot⟩
  rcases inv with ⟨he,hs,hcount,bound,model⟩
  change iter.end.val=64 at he
  change iter.start.val≤64 at hs
  change dot.count.val=iter.start.val at hcount
  change FJf_EbyKCodec.Bound dot at bound
  change FJf_EbyKCodec.model dot=FJj_ByteDotCell.sumPrefix f scratch iter.start.val at model
  cases out with
  | done r =>
    rcases r with ⟨status,dotOut⟩
    cases status with
    | Err e => trivial
    | Ok u =>
      unfold FIo_Native.weights.push_byte_products_loop.body at run
      obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases o with
      | none =>
        cases Result.ok.inj run
        have stop := FIp_RangeNone.none_next iter cursor hn
        have eq : iter.start.val=64 := by omega
        exact ⟨bound,by simpa only [eq] using hcount,by simpa only [eq] using model⟩
      | some j =>
        obtain ⟨we,hwe,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        obtain ⟨q,hq,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        obtain ⟨⟨r,dot1⟩,hp,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        cases r <;> cases run
  | cont next =>
    rcases next with ⟨cursor,next⟩
    obtain ⟨he',hs',more,bnext,cnext,mnext⟩ := FJj_ByteDotCell.value f scratch hc iter cursor dot next he bound run
    dsimp only [Inv]
    refine ⟨⟨by rw [he'];exact he,by omega,?_,bnext,?_⟩,?_⟩
    · rw [cnext,hcount,hs']
    · rw [mnext,model,hs']
      rfl
    · simp only [measure,he',hs'];omega
#print axioms step
end AspisR1.FJj_ByteDotStep
end
