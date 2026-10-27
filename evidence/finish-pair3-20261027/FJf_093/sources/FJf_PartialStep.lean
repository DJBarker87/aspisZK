import FJf_PartialCell
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJf_PartialStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NQ NE wide)
abbrev State := FIo_RangeNext.Range × FIo_Native.fast_pairing.EbyKDot
abbrev NativeResult := core.result.Result NE FIo_Native.verifier.Error

def Inv (f : Slice U8) (common : Array NQ 16#usize) (s : Usize) (t : State) : Prop :=
  t.1.end.val=16 ∧ t.1.start.val≤16 ∧ t.2.count.val=t.1.start.val ∧
  FJf_EbyKCodec.Bound t.2 ∧ FJf_EbyKCodec.model t.2=FJf_PartialCell.sumPrefix f common s t.1.start.val

def Post (f : Slice U8) (common : Array NQ 16#usize) (s : Usize) : NativeResult → Prop
  | .Err _ => True
  | .Ok out => FIo_WideValues.Canon out ∧ decodeWide (wide out)=FJf_PartialCell.sumPrefix f common s 16

def measure (t : State) : Nat := t.1.end.val-t.1.start.val

theorem step (f : Slice U8) (common : Array NQ 16#usize) (s : Usize)
    (hs : s.val < 4) (hc : FJf_QMArray.canon common) (t : State) (inv : Inv f common s t)
    (out : ControlFlow State NativeResult)
    (run : FIo_Native.weights.partial_dot_loop.body f common s t.1 t.2=ok out) :
    match out with
    | .done r => Post f common s r
    | .cont next => Inv f common s next ∧ measure next < measure t := by
  rcases t with ⟨iter,dot⟩
  dsimp only [Inv] at inv
  rcases inv with ⟨he,hstart,hcount,bound,model⟩
  cases out with
  | done result =>
    cases result with
    | Err e => trivial
    | Ok result =>
      unfold FIo_Native.weights.partial_dot_loop.body at run
      obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases o with
      | none =>
        obtain ⟨out,ho,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        cases Result.ok.inj run
        have stop := FIp_RangeNone.none_next iter cursor hn
        have eq : iter.start.val=16 := by omega
        have finish := FJf_EbyKFinish.value dot out ho
        exact ⟨finish.1,finish.2.trans (by simpa only [eq] using model)⟩
      | some j =>
        simp only [lift,bind_tc_ok] at run
        obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        obtain ⟨⟨r,_⟩,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
        cases r <;> cases run
  | cont next =>
    rcases next with ⟨cursor,next⟩
    obtain ⟨he',hs',more,bnext,cnext,mnext⟩ := FJf_PartialCell.value f common s hs hc iter cursor dot next he bound run
    dsimp only [Inv]
    refine ⟨⟨by rw [he'];exact he,by omega,?_,bnext,?_⟩,?_⟩
    · rw [cnext,hcount,hs']
    · rw [mnext,model,hs']
      rfl
    · simp only [measure,he',hs'];omega
#print axioms step
end AspisR1.FJf_PartialStep
end
