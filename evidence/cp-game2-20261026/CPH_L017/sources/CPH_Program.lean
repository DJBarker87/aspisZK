import Hist_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPH_Program
open Aeneas Aeneas.Std
/-- Selected verifier identity from the retained successful exact-default-ELF
loaded-program receipt (s9-h5-adoption-review, readonly/2/runtime/after).
L186's lowering2 source/ELF closure and retained P7 supply the external artifact
association; this definition adds no Lean trust or runtime-ID hypothesis.
This selection is specific to the recorded 7Q2nGsPg... deployment. -/
def verifier : S2W_ExtractionBoundary.Program :=
  Array.make 32#usize [95#u8, 12#u8, 126#u8, 84#u8, 84#u8, 184#u8, 191#u8, 44#u8, 127#u8, 237#u8, 85#u8, 250#u8, 26#u8, 65#u8, 11#u8, 162#u8, 234#u8, 180#u8, 193#u8, 149#u8, 162#u8, 190#u8, 100#u8, 247#u8, 226#u8, 253#u8, 59#u8, 0#u8, 225#u8, 151#u8, 154#u8, 141#u8]

theorem not_system : verifier ≠ Hist_Nonvacuity.key 0#u8 := by
  intro same
  have head := congrArg (fun key : S2W_ExtractionBoundary.Program => key.val[0]?) same
  change some (95#u8) = some (0#u8) at head
  exact (by decide : (95#u8) ≠ 0#u8) (Option.some.inj head)

#print axioms not_system
end AspisR1.CPH_Program
end
