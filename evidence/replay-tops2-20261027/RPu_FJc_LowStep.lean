import RPu_FJc_LowCell
import RPt_FIp_RangeNone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_LowStep
open Aeneas Aeneas.Std Result ControlFlow
open FIo_FieldBridge (NE)
abbrev State := FIo_RangeNext.Range × Array NE 16#usize

def Inv (ap0 ap1 : Array NE 4#usize) (s : State) : Prop :=
  FIo_ArrayCanon.Holds s.2 ∧ s.1.end.val=16 ∧ s.1.start.val≤16 ∧
  ∀ j,j<s.1.start.val → FIp_ArrayValue.value s.2 j=FJc_LowModel.value ap0 ap1 j

def Post (ap0 ap1 : Array NE 4#usize) (low : Array NE 16#usize) : Prop :=
  FIo_ArrayCanon.Holds low ∧ ∀ j,j<16 → FIp_ArrayValue.value low j=FJc_LowModel.value ap0 ap1 j

def measure (s : State) : Nat := s.1.end.val-s.1.start.val

theorem step (ap0 ap1 : Array NE 4#usize)
    (ha0 : FIo_ArrayCanon.Holds ap0) (ha1 : FIo_ArrayCanon.Holds ap1)
    (s : State) (inv : Inv ap0 ap1 s) (out : ControlFlow State (Array NE 16#usize))
    (run : FIo_Native.weights.Weights.pair_loop15.body ap0 ap1 s.1 s.2=ok out) :
    match out with
    | .done low => Post ap0 ap1 low
    | .cont t => Inv ap0 ap1 t ∧ measure t<measure s := by
  rcases s with ⟨iter,low⟩
  dsimp only [Inv] at inv
  cases out with
  | done result =>
    unfold FIo_Native.weights.Weights.pair_loop15.body at run
    obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases o with
    | none =>
      cases Result.ok.inj run
      have done := FIp_RangeNone.none_next iter cursor hn
      have stop : iter.start.val=16 := by have := inv.2.1;have := inv.2.2.1;omega
      exact ⟨inv.1,by simpa only [stop] using inv.2.2.2⟩
    | some i =>
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      obtain ⟨_,_,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases run
  | cont next =>
    rcases next with ⟨cursor,result⟩
    obtain ⟨he,hs,more,hc,hv⟩ := FJc_LowCell.value ap0 ap1 low result iter cursor ha0 ha1 inv.1 run
    refine ⟨⟨hc,?_,?_,?_⟩,?_⟩
    · rw [he];exact inv.2.1
    · have := inv.2.1;rw [hs];omega
    · intro j hj
      rw [hv]
      by_cases eq : iter.start.val=j
      · rw [if_pos eq]
      · rw [if_neg eq]
        exact inv.2.2.2 j (by rw [hs] at hj;omega)
    · simp only [measure,he,hs];omega
#print axioms step
end AspisR1.FJc_LowStep
end
