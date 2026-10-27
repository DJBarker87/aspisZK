import RPv_FJm_LibraStages
import RPu_FIp_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJm_LibraTotals
open Aeneas Aeneas.Std Result AspisR1CurrentWide.Proof
open FIo_FieldBridge (NE wide)

theorem value (terms : Array NE 4#usize) (hc : FIo_ArrayCanon.Holds terms) (first2 first3 all : NE)
    (run : FJm_LibraStages.totals terms=ok (first2,first3,all)) :
    FIo_WideValues.Canon first2 ∧ FIo_WideValues.Canon first3 ∧ FIo_WideValues.Canon all ∧
      decodeWide (wide first2)=FIp_ArrayValue.value terms 0+FIp_ArrayValue.value terms 1 ∧
      decodeWide (wide first3)=FIp_ArrayValue.value terms 0+FIp_ArrayValue.value terms 1+FIp_ArrayValue.value terms 2 ∧
      decodeWide (wide all)=FIp_ArrayValue.value terms 0+FIp_ArrayValue.value terms 1+
        FIp_ArrayValue.value terms 2+FIp_ArrayValue.value terms 3 := by
  unfold FJm_LibraStages.totals at run
  obtain ⟨t0,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨t1,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨two,htwo,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨t2,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨three,hthree,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨t3,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨four,hfour,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  cases Result.ok.inj run
  have c0 := FIo_ArrayCanon.read terms 0#usize t0 hc h0
  have c1 := FIo_ArrayCanon.read terms 1#usize t1 hc h1
  have c2 := FIo_ArrayCanon.read terms 2#usize t2 hc h2
  have c3 := FIo_ArrayCanon.read terms 3#usize t3 hc h3
  have v2 := FIo_WideValues.add t0 t1 first2 c0 c1 htwo
  have v3 := FIo_WideValues.add first2 t2 first3 v2.1 c2 hthree
  have v4 := FIo_WideValues.add first3 t3 all v3.1 c3 hfour
  have e0 := FIp_ArrayValue.read terms 0#usize t0 h0
  have e1 := FIp_ArrayValue.read terms 1#usize t1 h1
  have e2 := FIp_ArrayValue.read terms 2#usize t2 h2
  have e3 := FIp_ArrayValue.read terms 3#usize t3 h3
  simp only [show (0#usize).val=0 from by decide,show (1#usize).val=1 from by decide,
    show (2#usize).val=2 from by decide,show (3#usize).val=3 from by decide] at e0 e1 e2 e3
  refine ⟨v2.1,v3.1,v4.1,?_,?_,?_⟩
  · rw [v2.2,e0,e1]
  · rw [v3.2,v2.2,e0,e1,e2]
  · rw [v4.2,v3.2,v2.2,e0,e1,e2,e3]
#print axioms value
end AspisR1.FJm_LibraTotals
end
