import XRm_PowersCanonical
import XRl_DotAssociation
open Aeneas Aeneas.Std Result
open XRk_Release XRk_FieldExternal XRk_ResultTools XRm_WideProducer
namespace XRm_DotSites
 theorem unwrap_unit (r : core.result.Result Unit Unit) (out : Unit)
    (run : core.result.Result.unwrap core.fmt.DebugUnit r=ok out) : r=.Ok () := by
  cases r with
  | Ok x => cases x; rfl
  | Err e => simp [core.result.Result.unwrap] at run

/-- The three actual emitted EbyKDot push sites share one source-selected
chronological history. Canonicality comes from the supplied scratch producer,
not from the extracted WideExact carrier or arbitrary Reached history. -/
theorem tail (q : Array U8 608#usize) (g : Array XRk_Wide 29#usize)
    (slot : Usize) (out : XRk_Wide)
    (canonical : ∀ e ∈ g.val, Canonical e)
    (run : fast_dots.four_dots_one q g slot=ok out) :
    ∃ (xs : List XRl_DotHistory.Input) (d : fast_pairing.EbyKDot),
      XRl_DotHistory.Reached xs d ∧ xs.length=3 ∧
      (∀ v ∈ xs, Canonical v.1) ∧
      ∃ value total, fast_pairing.EbyKDot.finish d=ok total ∧
        aspis_core.field.wide_exact.WideExact.add value total=ok out := by
  unfold fast_dots.four_dots_one at run
  obtain ⟨iter,hiter,run⟩ := bind_success _ _ _ run
  obtain ⟨limbs1,hlimbs1,run⟩ := bind_success _ _ _ run
  obtain ⟨i,hi,run⟩ := bind_success _ _ _ run
  obtain ⟨m,hm,run⟩ := bind_success _ _ _ run
  obtain ⟨i1,hi1,run⟩ := bind_success _ _ _ run
  obtain ⟨m1,hm1,run⟩ := bind_success _ _ _ run
  obtain ⟨i2,hi2,run⟩ := bind_success _ _ _ run
  obtain ⟨m2,hm2,run⟩ := bind_success _ _ _ run
  obtain ⟨i3,hi3,run⟩ := bind_success _ _ _ run
  obtain ⟨m3,hm3,run⟩ := bind_success _ _ _ run
  obtain ⟨i4,hi4,run⟩ := bind_success _ _ _ run
  obtain ⟨m4,hm4,run⟩ := bind_success _ _ _ run
  obtain ⟨i5,hi5,run⟩ := bind_success _ _ _ run
  obtain ⟨m5,hm5,run⟩ := bind_success _ _ _ run
  obtain ⟨i6,hi6,run⟩ := bind_success _ _ _ run
  obtain ⟨m6,hm6,run⟩ := bind_success _ _ _ run
  obtain ⟨i7,hi7,run⟩ := bind_success _ _ _ run
  obtain ⟨m7,hm7,run⟩ := bind_success _ _ _ run
  obtain ⟨o,ho,run⟩ := bind_success _ _ _ run
  obtain ⟨value,hvalue,run⟩ := bind_success _ _ _ run
  obtain ⟨tail,htail,run⟩ := bind_success _ _ _ run
  obtain ⟨we,hwe,run⟩ := bind_success _ _ _ run
  obtain ⟨i8,hi8,run⟩ := bind_success _ _ _ run
  obtain ⟨i9,hi9,run⟩ := bind_success _ _ _ run
  obtain ⟨i10,hi10,run⟩ := bind_success _ _ _ run
  obtain ⟨s,hs,run⟩ := bind_success _ _ _ run
  obtain ⟨o1,ho1,run⟩ := bind_success _ _ _ run
  obtain ⟨q1,hq1,run⟩ := bind_success _ _ _ run
  obtain ⟨r,tail1,htail1,run⟩ := pair_bind_success _ _ _ run
  obtain ⟨unused1,hu1,run⟩ := bind_success _ _ _ run
  have accepted1 := unwrap_unit r unused1 hu1
  subst r
  simp only [core.result.Result.unwrap,bind_tc_ok] at run
  obtain ⟨i11,hi11,run⟩ := bind_success _ _ _ run
  obtain ⟨i12,hi12,run⟩ := bind_success _ _ _ run
  obtain ⟨i13,hi13,run⟩ := bind_success _ _ _ run
  obtain ⟨offset0,hoffset0,run⟩ := bind_success _ _ _ run
  obtain ⟨i14,hi14,run⟩ := bind_success _ _ _ run
  obtain ⟨we1,hwe1,run⟩ := bind_success _ _ _ run
  obtain ⟨i15,hi15,run⟩ := bind_success _ _ _ run
  obtain ⟨s1,hs1,run⟩ := bind_success _ _ _ run
  obtain ⟨o2,ho2,run⟩ := bind_success _ _ _ run
  obtain ⟨q2,hq2,run⟩ := bind_success _ _ _ run
  obtain ⟨r1,tail2,htail2,run⟩ := pair_bind_success _ _ _ run
  obtain ⟨unused2,hu2,run⟩ := bind_success _ _ _ run
  have accepted2 := unwrap_unit r1 unused2 hu2
  subst r1
  simp only [core.result.Result.unwrap,bind_tc_ok] at run
  obtain ⟨i16,hi16,run⟩ := bind_success _ _ _ run
  obtain ⟨i17,hi17,run⟩ := bind_success _ _ _ run
  obtain ⟨offset1,hoffset1,run⟩ := bind_success _ _ _ run
  obtain ⟨i18,hi18,run⟩ := bind_success _ _ _ run
  obtain ⟨we2,hwe2,run⟩ := bind_success _ _ _ run
  obtain ⟨i19,hi19,run⟩ := bind_success _ _ _ run
  obtain ⟨s2,hs2,run⟩ := bind_success _ _ _ run
  obtain ⟨o3,ho3,run⟩ := bind_success _ _ _ run
  obtain ⟨q3,hq3,run⟩ := bind_success _ _ _ run
  obtain ⟨r2,tail3,htail3,run⟩ := pair_bind_success _ _ _ run
  obtain ⟨unused3,hu3,run⟩ := bind_success _ _ _ run
  have accepted3 := unwrap_unit r2 unused3 hu3
  subst r2
  simp only [core.result.Result.unwrap,bind_tc_ok] at run
  obtain ⟨we3,hwe3,run⟩ := bind_success _ _ _ run
  refine ⟨[(we,q1),(we1,q2),(we2,q3)],tail3,?_,rfl,?_,value,we3,hwe3,run⟩
  · exact .push (.push (.push (.initial tail htail) we q1 htail1) we1 q2 htail2) we2 q3 htail3
  · intro v member
    simp only [List.mem_cons,List.mem_singleton] at member
    rcases member with first | second | third
    · subst v; exact XRm_PowersCanonical.array_read g _ we canonical hwe
    · subst v; exact XRm_PowersCanonical.array_read g _ we1 canonical hwe1
    · subst v; exact XRm_PowersCanonical.array_read g _ we2 canonical hwe2
#print axioms unwrap_unit
#print axioms tail
end XRm_DotSites
