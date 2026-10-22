import PoseidonExternalLazySourceCut
import Aeneas.Std.WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.PoseidonExternalColumn1CallEquation
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev U32 := Std.U32
abbrev U64 := Std.U64
abbrev Limbs := Array U32 4#usize
abbrev Sums := Array (Array U64 4#usize) 4#usize
abbrev Closure := state_only_poseidon.external_linear_lazy.closure_1

theorem source_eq (limbs : Limbs) (sums : Sums) (lane limb : Usize) :
    state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (limbs,sums,lane) limb = (do
        let i1 ← Array.index_usize limbs limb
        let i2 ← lift (core.convert.num.FromU64U32.from i1)
        let i3 ← lift (lane &&& 3#usize)
        let a2 ← Array.index_usize sums i3
        let i4 ← Array.index_usize a2 limb
        let i5 ← i2 + i4
        ok (i5,(limbs,sums,lane))) := by
  unfold state_only_poseidon.external_linear_lazy.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  simp only [lift, bind_tc_ok]
  rfl
#print axioms source_eq
end AspisR1.PoseidonExternalColumn1CallEquation
