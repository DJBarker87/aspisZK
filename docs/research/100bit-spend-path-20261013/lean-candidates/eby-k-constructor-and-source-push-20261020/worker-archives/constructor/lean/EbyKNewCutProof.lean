import AspisR1Stage2Accumulate.Funs
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace EbyKNewCutProof
theorem dot_new_zero :
    AspisR1Stage2Accumulate.fast_pairing.canonical.Dot.new =
      .ok { sums := Array.repeat 4#usize 0#u64 } := by
  rfl
theorem eby_k_new_zero :
    AspisR1Stage2Accumulate.fast_pairing.EbyKDot.new =
      .ok { c0 := { sums := Array.repeat 4#usize 0#u64 },
            c1 := { sums := Array.repeat 4#usize 0#u64 }, count := 0#usize } := by
  rfl
theorem public_entry_new_zero :
    AspisR1Stage2Accumulate.new_entry =
      .ok { c0 := { sums := Array.repeat 4#usize 0#u64 },
            c1 := { sums := Array.repeat 4#usize 0#u64 }, count := 0#usize } := by
  rfl
#print axioms dot_new_zero
#print axioms eby_k_new_zero
#print axioms public_entry_new_zero
end EbyKNewCutProof
