import R1Z.PV_RDB2C_PV_B2_C_RawWeights251Funs
set_option autoImplicit false
namespace PV_B2_F_RawFold
open Aeneas Aeneas.Std Result PV_B2_251c1
abbrev K := aspis_core.field.QM31

def tensor (factors : Array (Array K 4#usize) 5#usize) (j : Usize) : Result K :=
  [(0#usize,0#u32),(1#usize,2#u32),(2#usize,4#u32),(3#usize,6#u32),(4#usize,8#u32)].foldlM
    (fun (v : K) (ds : Usize × U32) => do
      let row ← Array.index_usize factors ds.1
      let factor ← Array.index_usize row (Usize.wrapping_shr j ds.2 &&& 3#usize)
      aspis_core.field.QM31.mul v factor) aspis_core.field.QM31.ONE

def point (points : Array K 10#usize) (r : Usize) : Result K :=
  [(9#usize,0#u32),(8#usize,1#u32),(7#usize,2#u32),(6#usize,3#u32),(5#usize,4#u32),(4#usize,5#u32),(3#usize,6#u32),(2#usize,7#u32),(1#usize,8#u32),(0#usize,9#u32)].foldlM
    (fun (v : K) (ib : Usize × U32) => do
      let q ← Array.index_usize points ib.1
      let factor ← host_weights.point_factor q r ib.2
      aspis_core.field.QM31.mul v factor) aspis_core.field.QM31.ONE

theorem tensor_source (factors : Array (Array K 4#usize) 5#usize) (j : Usize) :
    host_weights.tensor_raw factors j = tensor factors j := by
  dsimp only [host_weights.tensor_raw,tensor]
  simp only [List.foldlM_cons,List.foldlM_nil,bind_assoc,bind_pure,lift,bind_tc_ok]

theorem point_source (points : Array K 10#usize) (r : Usize) :
    host_weights.point_raw points r = point points r := by
  dsimp only [host_weights.point_raw,point]
  simp only [List.foldlM_cons,List.foldlM_nil,bind_assoc,bind_pure]
#print axioms tensor_source
#print axioms point_source
end PV_B2_F_RawFold
