import PoseidonExternalLazySourceCut
import Aeneas.Std.WP
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace AspisR1.PoseidonExternalColumnCallEquationV3
open Aeneas Aeneas.Std Result WP
open AspisR1SelectedMaskProbe
abbrev State := Array field.QM31 16#usize
abbrev Closure := state_only_poseidon.external_linear_lazy.closure.closure

theorem source_eq (state : State) (column limb : Usize) :
    state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
      (state,column) limb = (do
        let q ← Array.index_usize state column
        let a1 ← state_only_poseidon.extension_limbs q
        let i1 ← Array.index_usize a1 limb
        let i2 ← lift (core.convert.num.FromU64U32.from i1)
        let i3 ← 4#usize + column
        let q1 ← Array.index_usize state i3
        let a2 ← state_only_poseidon.extension_limbs q1
        let i4 ← Array.index_usize a2 limb
        let i5 ← lift (core.convert.num.FromU64U32.from i4)
        let i6 ← i2 + i5
        let i7 ← 8#usize + column
        let q2 ← Array.index_usize state i7
        let a3 ← state_only_poseidon.extension_limbs q2
        let i8 ← Array.index_usize a3 limb
        let i9 ← lift (core.convert.num.FromU64U32.from i8)
        let i10 ← i6 + i9
        let i11 ← 12#usize + column
        let q3 ← Array.index_usize state i11
        let a4 ← state_only_poseidon.extension_limbs q3
        let i12 ← Array.index_usize a4 limb
        let i13 ← lift (core.convert.num.FromU64U32.from i12)
        let i14 ← i10 + i13
        ok (i14,(state,column))) := by
  unfold state_only_poseidon.external_linear_lazy.closure.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU64.call_mut
  simp only [lift, bind_tc_ok]
  rfl
#print axioms source_eq
end AspisR1.PoseidonExternalColumnCallEquationV3
