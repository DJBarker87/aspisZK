import S7Kani3InverseLoop
set_option autoImplicit false
namespace S7Kani3GroupsLoop
open Aeneas Aeneas.Std Result
abbrev Group := Array U32 5#usize
def groups_owned
  (flat_inverse : alloc.vec.Vec U32)
  (groups : alloc.vec.Vec (Array U32 5#usize))
  (index : Std.Usize) (count : Std.Usize) :
  Result (alloc.vec.Vec (Array U32 5#usize))
  := do
  if index >= count
  then ok groups
  else
    let i ← 5#usize * index
    let m ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        U32) flat_inverse i
    let i1 ← i + 1#usize
    let m1 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        U32) flat_inverse i1
    let i2 ← i + 2#usize
    let m2 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        U32) flat_inverse i2
    let i3 ← i + 3#usize
    let m3 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        U32) flat_inverse i3
    let i4 ← i + 4#usize
    let m4 ←
      alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice
        U32) flat_inverse i4
    let groups1 ←
      alloc.vec.Vec.push groups (Array.make 5#usize [ m, m1, m2, m3, m4 ] :
        Array U32 5#usize)
    let i5 ← index + 1#usize
    groups_owned flat_inverse groups1 i5 count
partial_fixpoint


def record (flat : List U32) (i : Nat) : Group :=
  Array.make 5#usize [(flat[5*i]?.getD 0#u32),(flat[5*i+1]?.getD 0#u32),
    (flat[5*i+2]?.getD 0#u32),(flat[5*i+3]?.getD 0#u32),(flat[5*i+4]?.getD 0#u32)]
def model (flat : List U32) : Nat → Nat → List Group → List Group
 | 0,_,groups => groups
 | fuel+1,i,groups => model flat fuel (i+1) (groups++[record flat i])

theorem read_word (flat : alloc.vec.Vec U32) (i : Usize) (h : i.val<flat.val.length) :
    alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice U32) flat i =
      ok (flat.val[i.val]?.getD 0#u32) := by
  obtain ⟨x,hr,hx⟩ := WP.spec_imp_exists (alloc.vec.Vec.index_usize_spec flat i h)
  rw [List.getElem?_eq_getElem h]
  simpa only [Option.getD_some,hx] using hr

/-- Actual emitted five-read grouping driver, with complete ordinal order
and output lengths. The flat contents are unrestricted. -/
theorem groups_refines (flat : alloc.vec.Vec U32) (groups : alloc.vec.Vec Group)
    (index count : Usize) (fuel : Nat) (hc : count.val ≤ 22)
    (remaining : index.val+fuel=count.val) (hf : 5*count.val ≤ flat.val.length)
    (capacity : groups.val.length+fuel ≤ 22) :
    ∃ out, groups_owned flat groups index count=ok out ∧
      out.val=model flat.val fuel index.val groups.val ∧
      out.val.length=groups.val.length+fuel := by
  induction fuel generalizing groups index with
  | zero =>
      have stop : index ≥ count := by scalar_tac
      refine ⟨groups,?_,rfl,by omega⟩
      rw [groups_owned]; simp only [stop,if_pos]
  | succ fuel ih =>
      have running : ¬ index ≥ count := by scalar_tac
      obtain ⟨i,hi,hiv⟩ := AspisR1.ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (5*index.val) (by scalar_tac)
      have hmul : (5#usize*index : Result Usize)=ok i := hi
      obtain ⟨i1,hi1,hiv1⟩ := AspisR1.ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (i.val+1) (by scalar_tac)
      have hadd1 : (i+1#usize : Result Usize)=ok i1 := hi1
      obtain ⟨i2,hi2,hiv2⟩ := AspisR1.ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (i.val+2) (by scalar_tac)
      have hadd2 : (i+2#usize : Result Usize)=ok i2 := hi2
      obtain ⟨i3,hi3,hiv3⟩ := AspisR1.ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (i.val+3) (by scalar_tac)
      have hadd3 : (i+3#usize : Result Usize)=ok i3 := hi3
      obtain ⟨i4,hi4,hiv4⟩ := AspisR1.ExtractedCurrentReducerOps.tryMk_success
        (ty:=.Usize) (i.val+4) (by scalar_tac)
      have hadd4 : (i+4#usize : Result Usize)=ok i4 := hi4
      have hread := read_word flat i (by omega)
      have hread1 := read_word flat i1 (by omega)
      have hread2 := read_word flat i2 (by omega)
      have hread3 := read_word flat i3 (by omega)
      have hread4 := read_word flat i4 (by omega)
      have hcap : groups.val.length<Usize.max := by
        have hm : 22<Usize.max := by scalar_tac
        omega
      obtain ⟨groups1,hpush,hgroups1⟩ := WP.spec_imp_exists
        (alloc.vec.Vec.push_spec groups (record flat.val index.val) hcap)
      obtain ⟨index1,hinc,hindex1⟩ := S7Kani2AccumulatorLoop.increment index (by omega)
      have hlen1 : groups1.val.length=groups.val.length+1 := by
        rw [hgroups1,List.length_append]; rfl
      obtain ⟨out,hrun,hvalue,hlen⟩ := ih groups1 index1 (by omega) (by omega)
      refine ⟨out,?_,?_,by omega⟩
      · rw [groups_owned]
        simp only [running,if_false,hmul,hadd1,hadd2,hadd3,hadd4,
          hread,hread1,hread2,hread3,hread4,bind_tc_ok]
        simp only [hiv,hiv1,hiv2,hiv3,hiv4]
        change (do
          let groups1 ← alloc.vec.Vec.push groups (record flat.val index.val)
          let index1 ← index+1#usize
          groups_owned flat groups1 index1 count)=ok out
        simp only [hpush,hinc,bind_tc_ok]
        exact hrun
      · rw [hvalue,model,hindex1,hgroups1]

#print axioms read_word
#print axioms groups_refines
end S7Kani3GroupsLoop
