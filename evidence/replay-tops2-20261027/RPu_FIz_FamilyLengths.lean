import RPu_FIw_PublicModel
import R0P.Schedule
import R0P.Digest
import R0P.Value
import R0P.Occupancy
set_option autoImplicit false
namespace AspisR1.FIz_FamilyLengths
variable {K : Type} [Field K]
theorem schedule (p : R0P.Public K) (o : R0P.Openings K) (s : R0P.Sel K) :
    (R0P.scheduleFamily.residuals p o s).length=32 := by
  simp only [R0P.scheduleFamily,List.length_append,List.length_ofFn]
theorem path (p : R0P.Public K) (o : R0P.Openings K) (s : R0P.Sel K) :
    (R0P.pathFamily.residuals p o s).length=17 := by
  simp only [R0P.pathFamily,R0P.pathLanes,List.length_append,List.length_cons,List.length_nil,List.length_ofFn]
theorem value (p : R0P.Public K) (o : R0P.Openings K) (s : R0P.Sel K) :
    (R0P.valueFamily.residuals p o s).length=35 := by
  simp [R0P.valueFamily,R0P.valueRange]
theorem digest (p : R0P.Public K) (o : R0P.Openings K) (s : R0P.Sel K) :
    (R0P.digestFamily.residuals p o s).length=8 := by
  simp only [R0P.digestFamily,List.length_ofFn]
#print axioms schedule
#print axioms path
#print axioms value
#print axioms digest
end AspisR1.FIz_FamilyLengths
