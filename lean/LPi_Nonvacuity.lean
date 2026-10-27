import LPi_RawValues
import LPi_TowerValues
import LPi_WriterValues
set_option autoImplicit false
namespace AspisR1.LPi_Nonvacuity
open Aeneas Aeneas.Std Result LPi_FieldValues

theorem raw_zero_domain : LPi_RawValues.Canon (Array.make 4#usize [0#u32,0#u32,0#u32,0#u32]) := by
  norm_num [LPi_RawValues.Canon,Array.make]

theorem raw_one_domain : LPi_RawValues.Canon (Array.make 4#usize [1#u32,0#u32,0#u32,0#u32]) := by
  norm_num [LPi_RawValues.Canon,Array.make]

/-- A nonzero raw-input pair is in the exact concrete source domain.
This is local non-vacuity, not a joint inhabitant of headline premises. -/
theorem raw_nonzero_execution : ∃ r0 r1 r2 r3 : U64,
    FIo_Native.fast_pairing.canonical.Q.raw
      (Array.make 4#usize [1#u32,0#u32,0#u32,0#u32])
      (Array.make 4#usize [1#u32,0#u32,0#u32,0#u32]) =
      ok (Array.make 4#usize [r0,r1,r2,r3]) := by
  obtain ⟨r0,r1,r2,r3,run,_⟩ := LPi_RawValues.source _ _ raw_one_domain raw_one_domain
  exact ⟨r0,r1,r2,r3,run⟩

#print axioms raw_zero_domain
#print axioms raw_one_domain
#print axioms raw_nonzero_execution
end AspisR1.LPi_Nonvacuity
