import SDY_Loop
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_RowB
open SDY_Join_Release
abbrev RState := core.ops.range.Range Usize × Array U64 4#usize × aspis_core.field.M31
abbrev rb := verifier.update_residue_row_loop0.body
def limbs : Array U32 4#usize := ⟨[0#u32,0#u32,0#u32,0#u32],by simp⟩
def rs (s : RState) := rb limbs s.1 s.2.1 s.2.2
def row0 : Array U64 4#usize := ⟨[2147483648#u64,2147483649#u64,4294967296#u64,7#u64],by simp⟩
def row1 : Array U64 4#usize := ⟨[2147483648#u64,2147483649#u64,4294967296#u64,7#u64],by simp⟩
def row2 : Array U64 4#usize := ⟨[2147483648#u64,2147483649#u64,4294967296#u64,7#u64],by simp⟩
def row3 : Array U64 4#usize := ⟨[2147483648#u64,2147483649#u64,4294967296#u64,7#u64],by simp⟩
def row4 : Array U64 4#usize := ⟨[2147483648#u64,2147483649#u64,4294967296#u64,7#u64],by simp⟩
def power : aspis_core.field.QM31 := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def output : Array U64 4#usize := ⟨[1#u64,2#u64,2#u64,7#u64],by simp⟩
theorem rstep0 : rb limbs {start:=0#usize,«end»:=4#usize} row0 0#u32 = ok (.cont ({start:=1#usize,«end»:=4#usize},row1,0#u32)) := by
  unfold rb verifier.update_residue_row_loop0.body
  rw [SDY_Loop.range 0#usize 1#usize 4#usize (by decide) rfl]
  rfl
#print axioms rstep0
theorem rstep1 : rb limbs {start:=1#usize,«end»:=4#usize} row1 0#u32 = ok (.cont ({start:=2#usize,«end»:=4#usize},row2,0#u32)) := by
  unfold rb verifier.update_residue_row_loop0.body
  rw [SDY_Loop.range 1#usize 2#usize 4#usize (by decide) rfl]
  rfl
#print axioms rstep1
theorem rstep2 : rb limbs {start:=2#usize,«end»:=4#usize} row2 0#u32 = ok (.cont ({start:=3#usize,«end»:=4#usize},row3,0#u32)) := by
  unfold rb verifier.update_residue_row_loop0.body
  rw [SDY_Loop.range 2#usize 3#usize 4#usize (by decide) rfl]
  rfl
#print axioms rstep2
theorem rstep3 : rb limbs {start:=3#usize,«end»:=4#usize} row3 0#u32 = ok (.cont ({start:=4#usize,«end»:=4#usize},row4,0#u32)) := by
  unfold rb verifier.update_residue_row_loop0.body
  rw [SDY_Loop.range 3#usize 4#usize 4#usize (by decide) rfl]
  rfl
#print axioms rstep3
theorem rstep4 : rb limbs {start:=4#usize,«end»:=4#usize} row4 0#u32 = ok (.done row4) := by rfl
#print axioms rstep4
theorem rrun4 : loop rs ({start:=4#usize,«end»:=4#usize},row4,0#u32) = ok row4 := by
  exact SDY_Loop.done rs _ _ rstep4
#print axioms rrun4
theorem rrun3 : loop rs ({start:=3#usize,«end»:=4#usize},row3,0#u32) = ok row4 := by
  exact SDY_Loop.next rs _ _ _ rstep3 rrun4
#print axioms rrun3
theorem rrun2 : loop rs ({start:=2#usize,«end»:=4#usize},row2,0#u32) = ok row4 := by
  exact SDY_Loop.next rs _ _ _ rstep2 rrun3
#print axioms rrun2
theorem rrun1 : loop rs ({start:=1#usize,«end»:=4#usize},row1,0#u32) = ok row4 := by
  exact SDY_Loop.next rs _ _ _ rstep1 rrun2
#print axioms rrun1
theorem rrun0 : loop rs ({start:=0#usize,«end»:=4#usize},row0,0#u32) = ok row4 := by
  exact SDY_Loop.next rs _ _ _ rstep0 rrun1
#print axioms rrun0
abbrev Iter := core.slice.iter.IterMut U64
abbrev Back := Iter → Iter
abbrev State := Iter × Back
abbrev body := verifier.update_residue_row_loop1.body
def step (s : State) := body s.1 s.2
def it (i : Nat) : Iter := ⟨row4.to_slice,i⟩
def restore (i : Nat) (x : U64) : Back := fun r => {r with slice := r.slice.setAtNat i x}
def fin4 (b : Back) : Back := b
def fin3 (b : Back) : Back := fin4 (fun r => b (restore 3 7#u64 r))
def fin2 (b : Back) : Back := fin3 (fun r => b (restore 2 2#u64 r))
def fin1 (b : Back) : Back := fin2 (fun r => b (restore 1 2#u64 r))
def fin0 (b : Back) : Back := fin1 (fun r => b (restore 0 1#u64 r))
theorem step0 (b : Back) : step (it 0,b) = ok (.cont (it 1,fun r => b (restore 0 1#u64 r))) := by
  unfold step body verifier.update_residue_row_loop1.body
  simp [core.slice.iter.IteratorIterMut.next,it,row4,restore]
  rfl
#print axioms step0
theorem step1 (b : Back) : step (it 1,b) = ok (.cont (it 2,fun r => b (restore 1 2#u64 r))) := by
  unfold step body verifier.update_residue_row_loop1.body
  simp [core.slice.iter.IteratorIterMut.next,it,row4,restore]
  rfl
#print axioms step1
theorem step2 (b : Back) : step (it 2,b) = ok (.cont (it 3,fun r => b (restore 2 2#u64 r))) := by
  unfold step body verifier.update_residue_row_loop1.body
  simp [core.slice.iter.IteratorIterMut.next,it,row4,restore]
  rfl
#print axioms step2
theorem step3 (b : Back) : step (it 3,b) = ok (.cont (it 4,fun r => b (restore 3 7#u64 r))) := by
  unfold step body verifier.update_residue_row_loop1.body
  simp [core.slice.iter.IteratorIterMut.next,it,row4,restore]
  rfl
#print axioms step3
theorem step4 (b : Back) : step (it 4,b) = ok (.done b) := by
  unfold step body verifier.update_residue_row_loop1.body
  simp [core.slice.iter.IteratorIterMut.next,it,row4,restore]
  skip
#print axioms step4
theorem run4 (b : Back) : loop step (it 4,b) = ok (fin4 b) := by
  exact SDY_Loop.done step _ _ (step4 b)
#print axioms run4
theorem run3 (b : Back) : loop step (it 3,b) = ok (fin3 b) := by
  exact SDY_Loop.next step _ _ _ (step3 b) (run4 _)
#print axioms run3
theorem run2 (b : Back) : loop step (it 2,b) = ok (fin2 b) := by
  exact SDY_Loop.next step _ _ _ (step2 b) (run3 _)
#print axioms run2
theorem run1 (b : Back) : loop step (it 1,b) = ok (fin1 b) := by
  exact SDY_Loop.next step _ _ _ (step1 b) (run2 _)
#print axioms run1
theorem run0 (b : Back) : loop step (it 0,b) = ok (fin0 b) := by
  exact SDY_Loop.next step _ _ _ (step0 b) (run1 _)
#print axioms run0
theorem emitted : verifier.update_residue_row row0 power 0#u32 true = ok output := by
  unfold verifier.update_residue_row
  change (do let row ← loop rs ({start:=0#usize,«end»:=4#usize},row0,0#u32); let (iter,back) ← SDY_Join_intoIter row; let b ← verifier.update_residue_row_loop1 iter id; ok (back b)) = _
  rw [rrun0]
  simp only [bind_tc_ok]
  unfold SDY_Join_intoIter
  simp only [bind_tc_ok]
  change (do let b ← loop step (it 0,id); ok (Array.from_slice row4 (b (it 0)).slice)) = _
  rw [run0]
  rfl
#print axioms emitted
end SDY_RowB
