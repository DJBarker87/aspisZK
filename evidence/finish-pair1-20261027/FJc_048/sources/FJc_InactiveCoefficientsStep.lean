import FJc_InactiveCoefficientsModel
import FIo_GroupCoefficients
import FIp_RangeNone
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_InactiveCoefficientsStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open FJc_InactiveCoefficientsModel (group field sumPrefix)
abbrev State := FIo_GroupCoefficients.State

def Inv (f : Slice U8) (stop : Nat) (initial : Nat → AspisWideTower.WideExact) (s : State) : Prop :=
  FIo_ArrayCanon.Holds s.2 ∧ s.1.end.val=stop ∧ s.1.start.val≤stop ∧ stop≤64 ∧
  ∀ g, FIp_ArrayValue.value s.2 g=initial g+sumPrefix f g s.1.start.val

def Post (f : Slice U8) (stop : Nat) (initial : Nat → AspisWideTower.WideExact) (cs : FIo_GroupCoefficients.Cs) : Prop :=
  FIo_ArrayCanon.Holds cs ∧ ∀ g, FIp_ArrayValue.value cs g=initial g+sumPrefix f g stop

theorem step (f : Slice U8) (stop : Nat) (initial : Nat → AspisWideTower.WideExact)
    (s : State) (inv : Inv f stop initial s)
    (out : ControlFlow State FIo_GroupCoefficients.Cs)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop0.body f s.1 s.2=ok out) :
    match out with
    | .done cs => Post f stop initial cs
    | .cont t => Inv f stop initial t ∧ FIo_GroupCoefficients.measure t<FIo_GroupCoefficients.measure s := by
  rcases s with ⟨iter,cs⟩
  dsimp only [Inv] at inv
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop0.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    have h := FIp_RangeNone.none_next iter iter' hn
    have same : iter.start.val=stop := by have := inv.2.1;have := inv.2.2.1;omega
    exact ⟨inv.1,by simpa only [same] using inv.2.2.2.2⟩
  | some j =>
    obtain ⟨g,hg,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    obtain ⟨old,hold,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨v,hv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨sum,hsum,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have p := FIo_RangeNext.some_next iter iter' j hn
    have hj : j.val<64 := by rw [p.1];have := inv.2.1;have := inv.2.2.2.1;have := p.2.2.2;omega
    have co := FIo_ArrayCanon.read cs _ old inv.1 hold
    have cv := FIo_FieldCanonical.field f j v hv
    have vs := FIo_WideValues.add old v sum co cv hsum
    have updated := FIo_ArrayCanon.update cs next _ sum inv.1 vs.1 hnext
    have oldValue := FIp_ArrayValue.read cs _ old hold
    have vValue := FJc_InactiveCoefficientsModel.field_read f j v hj hv
    have gValue : (UScalar.cast .Usize g).val=group j.val := by
      rw [U8.cast_Usize_val_eq,FJc_InactiveCoefficientsModel.group_read j g hg]
    refine ⟨⟨updated,?_,?_,inv.2.2.2.1,?_⟩,?_⟩
    · rw [p.2.1];exact inv.2.1
    · have := inv.2.1;have := p.2.2.2;rw [p.2.2.1];omega
    · intro k
      rw [FJc_ArrayUpdateValue.value cs next _ sum k hnext,p.2.2.1,sumPrefix]
      by_cases eq : group j.val=k
      · have same : (UScalar.cast .Usize g).val=k := gValue.trans eq
        rw [if_pos same,vs.2,←oldValue,inv.2.2.2.2,←vValue]
        rw [←p.1,if_pos eq]
        rw [same]
        exact add_assoc _ _ _
      · have ne : (UScalar.cast .Usize g).val≠k := by rw [gValue];exact eq
        rw [if_neg ne,←p.1,if_neg eq,add_zero]
        simpa only [p.1] using inv.2.2.2.2 k
    · simp only [FIo_GroupCoefficients.measure,p.2.1,p.2.2.1];omega
#print axioms step
end AspisR1.FJc_InactiveCoefficientsStep
end
