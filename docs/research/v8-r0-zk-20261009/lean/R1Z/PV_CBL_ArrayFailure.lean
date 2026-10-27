import R1Z.PV_CBL_ArrayKernel
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_CBL_ArrayFailure
set_option autoImplicit false

theorem read_oob {T : Type} (v : Slice T) (i : Usize) (h : v.val.length ≤ i.val) :
    Slice.index_usize v i = fail .arrayOutOfBounds := by
  simp only [Slice.index_usize,Slice.getElem?_Usize_eq,List.getElem?_eq_none h]

theorem body_oob {T : Type} {N : Usize} (v : Slice T) (out : Array T N) (i : Usize)
    (hi : i.val<N.val) (hv : v.val.length ≤ i.val) :
    PV_CBL_ArrayKernel.array_reference_loop.body v out i=fail .arrayOutOfBounds := by
  have hn : i<N := hi
  simp only [PV_CBL_ArrayKernel.array_reference_loop.body,hn,if_true,
    read_oob v i hv,bind_tc_fail]
#print axioms read_oob
#print axioms body_oob
end R1Z.PV_CBL_ArrayFailure
