import FIp_Prefix
import FIp_RangeNone
import FIo_Constants
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIp_FinalSumStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
abbrev State := FIo_RangeNext.Range × NE

def Inv (parts k : Array NE 7#usize) (stop : Nat) (initial : AspisWideTower.WideExact) (s : State) : Prop :=
  FIo_WideValues.Canon s.2 ∧ s.1.end.val=stop ∧ s.1.start.val≤stop ∧
  decodeWide (wide s.2)=initial+FIp_Prefix.sumPrefix parts k s.1.start.val

def Post (parts k : Array NE 7#usize) (stop : Nat) (initial : AspisWideTower.WideExact) (z : NE) : Prop :=
  FIo_WideValues.Canon z ∧ decodeWide (wide z)=initial+FIp_Prefix.sumPrefix parts k stop

def measure (s : State) : Nat := s.1.end.val-s.1.start.val

theorem step (parts k : Array NE 7#usize) (hp : FIo_ArrayCanon.Holds parts) (hk : FIo_ArrayCanon.Holds k)
    (stop : Nat) (initial : AspisWideTower.WideExact) (s : State) (inv : Inv parts k stop initial s)
    (out : ControlFlow State NE)
    (run : FIo_Native.weights.Weights.pair_loop17.body parts k s.1 s.2=ok out) :
    match out with
    | .done z => Post parts k stop initial z
    | .cont t => Inv parts k stop initial t ∧ measure t<measure s := by
  rcases s with ⟨iter,sum⟩
  dsimp only [Inv] at inv
  unfold FIo_Native.weights.Weights.pair_loop17.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    have same : done sum=out := Result.ok.inj run
    subst out
    have hn := FIp_RangeNone.none_next iter iter' hn
    have same : iter.start.val=stop := by change _≤_ at hn; have := inv.2.1; have := inv.2.2.1; omega
    exact ⟨inv.1,by simpa only [same] using inv.2.2.2⟩
  | some i =>
    obtain ⟨p,hpRead,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [FIo_Native.trace.value,bind_tc_ok] at run
    obtain ⟨power,hkRead,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hmul,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨next,hadd,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    have same : cont (iter',next)=out := Result.ok.inj run
    subst out
    have vp := FIo_ArrayCanon.read parts i p hp hpRead
    have vk := FIo_ArrayCanon.read k i power hk hkRead
    have vm := FIo_WideMulValues.mul power p product vk vp hmul
    have va := FIo_WideValues.add sum product next inv.1 vm.1 hadd
    have progress := FIo_RangeNext.some_next iter iter' i hn
    have pe := FIp_ArrayValue.read parts i p hpRead
    have ke := FIp_ArrayValue.read k i power hkRead
    refine ⟨⟨va.1,?_,?_,?_⟩,?_⟩
    · simpa only [progress.2.1] using inv.2.1
    · have h := progress.2.2.2; have h' := inv.2.1
      simp only [progress.2.2.1]; omega
    · rw [va.2,vm.2,inv.2.2.2,progress.2.2.1,FIp_Prefix.succ,←pe,←ke,progress.1]
      simp only [add_assoc]
    · simp only [measure,progress.2.1,progress.2.2.1]
      have := progress.2.2.2
      omega

#print axioms step
end AspisR1.FIp_FinalSumStep
end
