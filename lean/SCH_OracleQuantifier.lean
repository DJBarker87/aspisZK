import SdkC_Oracle
set_option autoImplicit false
namespace AspisR1.SCH_OracleQuantifier
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem fixed_world (sha H : Bytes → State) (p1 : S2W_ExtractionBoundary.P1 sha H) :
    sha = H := funext p1.realization

/-- The P1 observation in Rc7 is indexed by its supplied world. Reusing that
fixed native observation for every oracle would contradict the actual P1 type. -/
theorem not_all_worlds (sha : Bytes → State) :
    ¬ ∀ H : Bytes → State, S2W_ExtractionBoundary.P1 sha H := by
  intro every
  have zero := congrFun ((every (fun _ _ => 0)).realization []) 0
  have one := congrFun ((every (fun _ _ => 1)).realization []) 0
  have different : (0 : AspisV8R19.DuplexFrames.Byte) ≠ 1 := by decide
  exact different (zero.symm.trans one)

#print axioms fixed_world
#print axioms not_all_worlds
end AspisR1.SCH_OracleQuantifier
