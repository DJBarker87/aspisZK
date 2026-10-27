import FJc_LowModel
import FJc_ArrayUpdateValue
import FIo_RangeNext
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_LowCell
open Aeneas Aeneas.Std Result ControlFlow AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)
/-- VALUE of one write in the actual two-fold low challenge constructor. -/
theorem value (ap0 ap1 : Array NE 4#usize) (low next : Array NE 16#usize)
    (iter iter' : FIo_RangeNext.Range)
    (ha0 : FIo_ArrayCanon.Holds ap0) (ha1 : FIo_ArrayCanon.Holds ap1)
    (hlow : FIo_ArrayCanon.Holds low)
    (run : FIo_Native.weights.Weights.pair_loop15.body ap0 ap1 iter low=ok (.cont (iter',next))) :
    iter'.end=iter.end ∧ iter'.start.val=iter.start.val+1 ∧ iter.start.val< iter.end.val ∧
    FIo_ArrayCanon.Holds next ∧
    ∀ j,FIp_ArrayValue.value next j=
      if iter.start.val=j then FJc_LowModel.value ap0 ap1 j else FIp_ArrayValue.value low j := by
  unfold FIo_Native.weights.Weights.pair_loop15.body at run
  obtain ⟨⟨o,cursor⟩,hn,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases o with
  | none => cases run
  | some s =>
    obtain ⟨a,ha,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨ai,hai,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨av,hav,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨b,hb,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨bi,hbi,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨bv,hbv,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨product,hproduct,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨scalar,hscalar,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨scaled,hscaled,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    obtain ⟨updated,hupdated,run⟩ := Port3_PushFrame.bind_success _ _ _ run
    cases Result.ok.inj run
    have ca := FIo_ArrayCanon.read ap0 ai av ha0 hav
    have cb := FIo_ArrayCanon.read ap1 bi bv ha1 hbv
    have vp := FIo_WideMulValues.mul av bv product ca cb hproduct
    have scalarValue := FIo_M31Values.mul _ _ scalar hscalar
    have vs := FGm_WideScaleValue.value product scaled scalar hscaled
    have progress := FIo_RangeNext.some_next iter iter' s hn
    have vi := FJc_DigitIndices.rem4 s a ha
    have vj := FJc_DigitIndices.div4 s b hb
    have pi := FJc_LowModel.perm_read a ai hai
    have pj := FJc_LowModel.perm_read b bi hbi
    have model : decodeWide (wide scaled)=FJc_LowModel.value ap0 ap1 s.val := by
      rw [vs.2,scalarValue.2,vp.2,←FIp_ArrayValue.read ap0 ai av hav,
        ←FIp_ArrayValue.read ap1 bi bv hbv,←pi,←pj,vi,vj]
      rfl
    refine ⟨progress.2.1,progress.2.2.1,progress.2.2.2,
      FIo_ArrayCanon.update low next s scaled hlow vs.1 hupdated,?_⟩
    intro j
    rw [FJc_ArrayUpdateValue.value low next s scaled j hupdated,model,progress.1]
    by_cases eq : iter.start.val=j
    · simp only [if_pos eq,eq]
    · simp only [if_neg eq]
#print axioms value
end AspisR1.FJc_LowCell
end
