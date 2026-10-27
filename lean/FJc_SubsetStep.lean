import FJc_SubsetModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_SubsetStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
open FJc_SubsetModel (mask sumPrefix)
abbrev State := FIo_GroupSubset.State

def Inv (low : Array NE 16#usize) (group stop : Nat) (initial : AspisWideTower.WideExact) (s : State) : Prop :=
  FIo_WideValues.Canon s.2 ∧ s.1.end.val=stop ∧ s.1.start.val≤stop ∧ stop≤16 ∧
  decodeWide (wide s.2)=initial+sumPrefix low group s.1.start.val

def Post (low : Array NE 16#usize) (group stop : Nat) (initial : AspisWideTower.WideExact) (out : NE) : Prop :=
  FIo_WideValues.Canon out ∧ decodeWide (wide out)=initial+sumPrefix low group stop

theorem step (low : Array NE 16#usize) (group : Usize) (hlow : FIo_ArrayCanon.Holds low)
    (stop : Nat) (initial : AspisWideTower.WideExact) (s : State)
    (inv : Inv low group.val stop initial s) (out : ControlFlow State NE)
    (run : FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body low group s.1 s.2=ok out) :
    match out with
    | .done w => Post low group.val stop initial w
    | .cont t => Inv low group.val stop initial t ∧ FIo_GroupSubset.measure t<FIo_GroupSubset.measure s := by
  rcases s with ⟨iter,w⟩
  dsimp only [Inv] at inv
  unfold FIo_Native.weights.s2_grouped_inactive_pair_loop1_loop0.body at run
  obtain ⟨⟨o,iter'⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none =>
    cases Result.ok.inj run
    have h := FIp_RangeNone.none_next iter iter' hn
    have hs : iter.start.val=stop := by have := inv.2.1;have := inv.2.2.1;omega
    exact ⟨inv.1,by simpa only [hs] using inv.2.2.2.2⟩
  | some bit =>
    obtain ⟨challenge,hchallenge,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨m,hm,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨shifted,hshift,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    simp only [lift,bind_tc_ok] at run
    have p := FIo_RangeNext.some_next iter iter' bit hn
    have hb : bit.val<16 := by rw [p.1];have := inv.2.1;have := inv.2.2.2.1;have := p.2.2.2;omega
    have decrease : ∀ z : NE, FIo_GroupSubset.measure (iter',z)<FIo_GroupSubset.measure (iter,w) := by
      intro z
      simp only [FIo_GroupSubset.measure,p.2.1,p.2.2.1];omega
    have hmask := FJc_SubsetModel.mask_read group m hm
    have selected := FJc_MaskBits.selected m shifted bit hb hshift
    have challengeCanon := FIo_ArrayCanon.read low bit challenge hlow hchallenge
    have challengeValue := FIp_ArrayValue.read low bit challenge hchallenge
    split at run
    · rename_i yes
      have hy : (m &&& shifted)≠0#u16 := by simpa using yes
      have hsel : (mask group.val &&& 2^iter.start.val)≠0 := by rw [hmask,←p.1];exact selected.mp hy
      obtain ⟨next,hnext,run⟩ := Port3_PushFrame.bind_success _ _ _ run
      cases Result.ok.inj run
      have va := FIo_WideValues.add w challenge next inv.1 challengeCanon hnext
      refine ⟨⟨va.1,?_,?_,inv.2.2.2.1,?_⟩,decrease next⟩
      · rw [p.2.1];exact inv.2.1
      · have := inv.2.1;have := p.2.2.2;rw [p.2.2.1];omega
      · rw [va.2,inv.2.2.2.2,p.2.2.1,sumPrefix,if_pos hsel,←challengeValue,p.1]
        exact add_assoc _ _ _
    · rename_i no
      have hnsel : ¬(m &&& shifted)≠0#u16 := by simpa using no
      have hsel : ¬(mask group.val &&& 2^iter.start.val)≠0 := by rw [hmask,←p.1];exact fun h=>hnsel (selected.mpr h)
      cases Result.ok.inj run
      refine ⟨⟨inv.1,?_,?_,inv.2.2.2.1,?_⟩,decrease w⟩
      · rw [p.2.1];exact inv.2.1
      · have := inv.2.1;have := p.2.2.2;rw [p.2.2.1];omega
      · rw [p.2.2.1,sumPrefix,if_neg hsel,add_zero];exact inv.2.2.2.2
#print axioms step
end AspisR1.FJc_SubsetStep
end
