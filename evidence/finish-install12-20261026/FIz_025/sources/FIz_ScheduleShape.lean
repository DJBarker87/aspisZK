import R0P.Schedule
set_option autoImplicit false
namespace AspisR1.FIz_ScheduleShape
variable {K : Type} [Field K]
theorem value (v : R0P.Variant) (o : R0P.Openings K) (s : R0P.Sel K) (j : Fin 16) :
    R0P.scheduleInitial v o s j =
      let high := R0P.g2High s
      let low := R0P.g2Low s
      let vs := R0P.scheduleVariantSelectors v (high 27) (high 28) (high 29)
      let full := low 0*((((high 0+high 1)+high 25)+high 30+vs.1)+vs.2.1)
      let initial := (if j.val<8 then full+low 0*R0P.scheduleNodes s else full)*o.z j
      let domain := (high 0*(1095958529 : K)+((high 1+high 30)+vs.1)*(1095958531 : K))+high 25*(1095958530 : K)
      let len := (high 0*(8 : K)+((high 1+high 30)+vs.1)*(18 : K))+high 25*(16 : K)
      if j.val=9 then initial-low 0*len else if j.val=8 then initial-low 0*domain else initial := by
  unfold R0P.scheduleInitial
  simp only [Fin.ext_iff,show (8 : Fin 16).val=8 from rfl,show (9 : Fin 16).val=9 from rfl]
  by_cases h8 : j.val=8 <;> by_cases h9 : j.val=9 <;>
    simp_all only [↓reduceIte] <;> try omega <;> split_ifs <;> rfl
#print axioms value
end AspisR1.FIz_ScheduleShape
