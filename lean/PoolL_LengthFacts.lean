import PoolL_LengthSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolL_LengthFacts
open Aeneas Aeneas.Std Result PoolL_LengthSource

theorem exact (data : Slice U8) (size : Usize) :
    lengthPrefix data size =
      (if (Slice.len data) != size then
        ok (core.result.Result.Err
          (AdapterRw.solana_program_error.ProgramError.Custom 1095966721#u32))
      else ok (core.result.Result.Ok ())) := by
  simp [lengthPrefix,
    PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError,
    PoolM_NativeCancelSource.solana_program_error.ProgramError.Insts.CoreConvertFromPoolV1ProgramError.from]

/-- No header reads or arithmetic can be reached past this length cut. -/
theorem wrong (data : Slice U8) (size : Usize) (h : data.val.length ≠ size.val) :
    lengthPrefix data size =
      ok (.Err (.Custom 1095966721#u32)) := by
  rw [exact]
  simp [Slice.len,h]

#print axioms exact
#print axioms wrong
end AspisR1.PoolL_LengthFacts
end
