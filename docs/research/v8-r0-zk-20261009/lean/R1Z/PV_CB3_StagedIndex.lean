import R1Z.PV_CB3_StagedTotal
set_option autoImplicit false
namespace R1Z.PV_CB3_StagedIndex
open Aeneas Aeneas.Std Result

def limb (a : Array U32 8#usize) (i : Fin 8) : U32 :=
  a.val[i.val]'(by rw [a.property]; exact i.isLt)

theorem read0 (a : Array U32 8#usize) :
    Array.index_usize a 0#usize = ok (limb a ⟨0,by decide⟩) :=
  PV_CB3_StagedTotal.read_eq a 0#usize (by decide)

theorem read1 (a : Array U32 8#usize) :
    Array.index_usize a 1#usize = ok (limb a ⟨1,by decide⟩) :=
  PV_CB3_StagedTotal.read_eq a 1#usize (by decide)

theorem read2 (a : Array U32 8#usize) :
    Array.index_usize a 2#usize = ok (limb a ⟨2,by decide⟩) :=
  PV_CB3_StagedTotal.read_eq a 2#usize (by decide)

theorem read3 (a : Array U32 8#usize) :
    Array.index_usize a 3#usize = ok (limb a ⟨3,by decide⟩) :=
  PV_CB3_StagedTotal.read_eq a 3#usize (by decide)

theorem read4 (a : Array U32 8#usize) :
    Array.index_usize a 4#usize = ok (limb a ⟨4,by decide⟩) :=
  PV_CB3_StagedTotal.read_eq a 4#usize (by decide)

theorem read5 (a : Array U32 8#usize) :
    Array.index_usize a 5#usize = ok (limb a ⟨5,by decide⟩) :=
  PV_CB3_StagedTotal.read_eq a 5#usize (by decide)

theorem read6 (a : Array U32 8#usize) :
    Array.index_usize a 6#usize = ok (limb a ⟨6,by decide⟩) :=
  PV_CB3_StagedTotal.read_eq a 6#usize (by decide)

theorem read7 (a : Array U32 8#usize) :
    Array.index_usize a 7#usize = ok (limb a ⟨7,by decide⟩) :=
  PV_CB3_StagedTotal.read_eq a 7#usize (by decide)

#print axioms read0
#print axioms read1
#print axioms read2
#print axioms read3
#print axioms read4
#print axioms read5
#print axioms read6
#print axioms read7
end R1Z.PV_CB3_StagedIndex
