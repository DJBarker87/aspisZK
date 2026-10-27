import SDY_Loop
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_RowA
open SDY_Join_Release
abbrev RState := core.ops.range.Range Usize × Array U64 4#usize × aspis_core.field.M31
abbrev rb := verifier.update_residue_row_loop0.body
def limbs : Array U32 4#usize := ⟨[1#u32,2#u32,3#u32,4#u32],by simp⟩
def rs (s : RState) := rb limbs s.1 s.2.1 s.2.2
def row0 : Array U64 4#usize := ⟨[1#u64,2#u64,3#u64,4#u64],by simp⟩
def row1 : Array U64 4#usize := ⟨[3#u64,2#u64,3#u64,4#u64],by simp⟩
def row2 : Array U64 4#usize := ⟨[3#u64,6#u64,3#u64,4#u64],by simp⟩
def row3 : Array U64 4#usize := ⟨[3#u64,6#u64,9#u64,4#u64],by simp⟩
def row4 : Array U64 4#usize := ⟨[3#u64,6#u64,9#u64,12#u64],by simp⟩
def power : aspis_core.field.QM31 := ⟨⟨1#u32,2#u32⟩,⟨3#u32,4#u32⟩⟩
def output : Array U64 4#usize := ⟨[3#u64,6#u64,9#u64,12#u64],by simp⟩
theorem rstep0 : rb limbs {start:=0#usize,«end»:=4#usize} row0 2#u32 = ok (.cont ({start:=1#usize,«end»:=4#usize},row1,2#u32)) := by
  unfold rb verifier.update_residue_row_loop0.body
  rw [SDY_Loop.range 0#usize 1#usize 4#usize (by decide) rfl]
  rfl
#print axioms rstep0
theorem rstep1 : rb limbs {start:=1#usize,«end»:=4#usize} row1 2#u32 = ok (.cont ({start:=2#usize,«end»:=4#usize},row2,2#u32)) := by
  unfold rb verifier.update_residue_row_loop0.body
  rw [SDY_Loop.range 1#usize 2#usize 4#usize (by decide) rfl]
  rfl
#print axioms rstep1
theorem rstep2 : rb limbs {start:=2#usize,«end»:=4#usize} row2 2#u32 = ok (.cont ({start:=3#usize,«end»:=4#usize},row3,2#u32)) := by
  unfold rb verifier.update_residue_row_loop0.body
  rw [SDY_Loop.range 2#usize 3#usize 4#usize (by decide) rfl]
  rfl
#print axioms rstep2
theorem rstep3 : rb limbs {start:=3#usize,«end»:=4#usize} row3 2#u32 = ok (.cont ({start:=4#usize,«end»:=4#usize},row4,2#u32)) := by
  unfold rb verifier.update_residue_row_loop0.body
  rw [SDY_Loop.range 3#usize 4#usize 4#usize (by decide) rfl]
  rfl
#print axioms rstep3
theorem rstep4 : rb limbs {start:=4#usize,«end»:=4#usize} row4 2#u32 = ok (.done row4) := by rfl
#print axioms rstep4
theorem rrun4 : loop rs ({start:=4#usize,«end»:=4#usize},row4,2#u32) = ok row4 := by
  exact SDY_Loop.done rs _ _ rstep4
#print axioms rrun4
theorem rrun3 : loop rs ({start:=3#usize,«end»:=4#usize},row3,2#u32) = ok row4 := by
  exact SDY_Loop.next rs _ _ _ rstep3 rrun4
#print axioms rrun3
theorem rrun2 : loop rs ({start:=2#usize,«end»:=4#usize},row2,2#u32) = ok row4 := by
  exact SDY_Loop.next rs _ _ _ rstep2 rrun3
#print axioms rrun2
theorem rrun1 : loop rs ({start:=1#usize,«end»:=4#usize},row1,2#u32) = ok row4 := by
  exact SDY_Loop.next rs _ _ _ rstep1 rrun2
#print axioms rrun1
theorem rrun0 : loop rs ({start:=0#usize,«end»:=4#usize},row0,2#u32) = ok row4 := by
  exact SDY_Loop.next rs _ _ _ rstep0 rrun1
#print axioms rrun0
theorem emitted : verifier.update_residue_row row0 power 2#u32 false = ok output := by
  unfold verifier.update_residue_row
  change (do let row ← loop rs ({start:=0#usize,«end»:=4#usize},row0,2#u32); ok row) = _
  rw [rrun0]
  rfl
#print axioms emitted
end SDY_RowA
