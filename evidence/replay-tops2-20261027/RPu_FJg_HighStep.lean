import RPu_FJg_HighCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJg_HighStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)
abbrev State := FIo_RangeNext.Range × FIo_Native.fast_pairing.EbyKDot
abbrev NativeResult := core.result.Result NE FIo_Native.verifier.Error

def Inv (f : Array NE 4#usize) (common : Array NQ 4#usize) (t : State) : Prop :=
  t.1.end.val=4 ∧ t.1.start.val≤4 ∧ t.2.count.val=t.1.start.val ∧
  FJf_EbyKCodec.Bound t.2 ∧ FJf_EbyKCodec.model t.2=FJg_HighCell.sumPrefix f common t.1.start.val

def Post (f : Array NE 4#usize) (common : Array NQ 4#usize) : NativeResult → Prop
  | .Err _ => True
  | .Ok out => FIo_WideValues.Canon out ∧ decodeWide (wide out)=FJg_HighCell.sumPrefix f common 4

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (f : Array NE 4#usize) (common : Array NQ 4#usize)
    (hf : FIo_ArrayCanon.Holds f) (hc : FJf_QMArray.canon common) (t : State) (inv : Inv f common t)
    (out : ControlFlow State NativeResult)
    (run : FIo_Native.weights.high_dot_loop.body f common t.1 t.2=ok out) :
    match out with
    | .done r => Post f common r
    | .cont next => Inv f common next ∧ measure next < measure t := by
  rcases t with ⟨iter,dot⟩
  dsimp only [Inv] at inv
  rcases inv with ⟨he,hstart,hcount,bound,model⟩
  cases out with
  | done result =>
    cases result with
    | Err e => trivial
    | Ok result =>
      unfold FIo_Native.weights.high_dot_loop.body at run
      obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases o with
      | none =>
        obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        cases Result.ok.inj run
        have stop := FIp_RangeNone.none_next iter cursor hn
        have eq : iter.start.val=4 := by omega
        have finish := FJf_EbyKFinish.value dot _ ho
        exact ⟨finish.1,finish.2.trans (by simpa only [eq] using model)⟩
      | some j =>
        obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        obtain ⟨⟨r,_⟩,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        cases r <;> cases run
  | cont next =>
    rcases next with ⟨cursor,next⟩
    obtain ⟨he',hs',more,bnext,cnext,mnext⟩ := FJg_HighCell.value f common hf hc iter cursor dot next bound run
    dsimp only [Inv]
    refine ⟨⟨by rw [he'];exact he,by omega,?_,bnext,?_⟩,?_⟩
    · rw [cnext,hcount,hs']
    · rw [mnext,model,hs']
      rfl
    · simp only [measure,he',hs'];omega
#print axioms step
end AspisR1.FJg_HighStep
end
