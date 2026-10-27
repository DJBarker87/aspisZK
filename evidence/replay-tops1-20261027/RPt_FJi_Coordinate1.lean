import RPt_FJi_LaneValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJi_Coordinate1
open Aeneas Aeneas.Std Result
open FJi_Accumulations FJi_LaneValue
open FJf_U64Array (cell)
/-- Coordinate 1 VALUE of the complete installed eight-update term suffix. -/
theorem value (c : Coefficients) (a : U32) (s out : Sums)
    (run : accumulate c a s=ok out) :
    (cell out 1).val=(cell s 1).val+(word c 1).val*a.val := by
  rw [enumeration] at run
  obtain ⟨s1,h0,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s2,h1,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s3,h2,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s4,h3,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s5,h4,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s6,h5,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s7,h6,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  obtain ⟨s8,h7,run⟩ := Port3_PushFrame.bind_success _ _ _ run
  have same : out=s8 := (Result.ok.inj run).symm
  subst out
  have v0 := FJi_LaneValue.value c a s s1 0#usize h0 1
  change (cell s1 1).val=(if 0=1 then (cell s 1).val+(word c 1).val*a.val else (cell s 1).val) at v0
  rw [if_neg (by decide)] at v0
  have v1 := FJi_LaneValue.value c a s1 s2 1#usize h1 1
  change (cell s2 1).val=(if 1=1 then (cell s1 1).val+(word c 1).val*a.val else (cell s1 1).val) at v1
  rw [if_pos (by decide)] at v1
  have v2 := FJi_LaneValue.value c a s2 s3 2#usize h2 1
  change (cell s3 1).val=(if 2=1 then (cell s2 1).val+(word c 1).val*a.val else (cell s2 1).val) at v2
  rw [if_neg (by decide)] at v2
  have v3 := FJi_LaneValue.value c a s3 s4 3#usize h3 1
  change (cell s4 1).val=(if 3=1 then (cell s3 1).val+(word c 1).val*a.val else (cell s3 1).val) at v3
  rw [if_neg (by decide)] at v3
  have v4 := FJi_LaneValue.value c a s4 s5 4#usize h4 1
  change (cell s5 1).val=(if 4=1 then (cell s4 1).val+(word c 1).val*a.val else (cell s4 1).val) at v4
  rw [if_neg (by decide)] at v4
  have v5 := FJi_LaneValue.value c a s5 s6 5#usize h5 1
  change (cell s6 1).val=(if 5=1 then (cell s5 1).val+(word c 1).val*a.val else (cell s5 1).val) at v5
  rw [if_neg (by decide)] at v5
  have v6 := FJi_LaneValue.value c a s6 s7 6#usize h6 1
  change (cell s7 1).val=(if 6=1 then (cell s6 1).val+(word c 1).val*a.val else (cell s6 1).val) at v6
  rw [if_neg (by decide)] at v6
  have v7 := FJi_LaneValue.value c a s7 s8 7#usize h7 1
  change (cell s8 1).val=(if 7=1 then (cell s7 1).val+(word c 1).val*a.val else (cell s7 1).val) at v7
  rw [if_neg (by decide)] at v7
  rw [v7,v6,v5,v4,v3,v2,v1,v0]
#print axioms value
end AspisR1.FJi_Coordinate1
end
