import SDY_Slice
import AdapterRwScalar
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_MpA
open SDY_Join_Release AspisR1.AdapterRw.Scalar
abbrev Node := Array U8 32#usize
def node (x : U8) : Node := Array.repeat 32#usize x
def copyUnit : core.marker.Copy Unit := {cloneInst := {clone := fun x => ok x}}
def hash : aspis_core.digest.Digest32 Unit := {coremarkerCopyInst := copyUnit,digest := fun _ parts => ok (node ((parts.val[1]?.map (fun s => s.val[0]?.getD 0#u8)).getD 0#u8))}
def idx : Array U32 16#usize := ⟨8#u32 :: List.replicate 15 0#u32,by simp⟩
def val : Array Node 16#usize := ⟨node 5#u8 :: List.replicate 15 (node 0#u8),by simp⟩
def outidx : Array U32 16#usize := ⟨1#u32 :: List.replicate 15 0#u32,by simp⟩
def outval : Array Node 16#usize := ⟨node 5#u8 :: List.replicate 15 (node 0#u8),by simp⟩
def nodes : Slice U8 := SDY_Slice.nodes 2#u8
abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.IterMut Node)
abbrev Back := Iter → Iter
abbrev State := Iter × Back × Usize × Usize
abbrev body := multiproof.verify_in_place_loop0_loop0_loop0.body
def children : Array Node 8#usize := Array.repeat 8#usize (node 0#u8)
def it (j : Usize) : Iter := ⟨⟨children.to_slice,j.val⟩,j⟩
def restore (j : Nat) (v : Node) : Back := fun r => {r with iter := {r.iter with slice := r.iter.slice.setAtNat j v}}
def step (s : State) := body idx val 1#usize nodes 1#u32 none s.1 s.2.1 s.2.2.1 s.2.2.2
def fin8 (b : Back) : Back := b
def fin7 (b : Back) : Back := fin8 (fun r => b (restore 7 (node 2#u8) r))
def fin6 (b : Back) : Back := fin7 (fun r => b (restore 6 (node 2#u8) r))
def fin5 (b : Back) : Back := fin6 (fun r => b (restore 5 (node 2#u8) r))
def fin4 (b : Back) : Back := fin5 (fun r => b (restore 4 (node 2#u8) r))
def fin3 (b : Back) : Back := fin4 (fun r => b (restore 3 (node 2#u8) r))
def fin2 (b : Back) : Back := fin3 (fun r => b (restore 2 (node 2#u8) r))
def fin1 (b : Back) : Back := fin2 (fun r => b (restore 1 (node 2#u8) r))
def fin0 (b : Back) : Back := fin1 (fun r => b (restore 0 (node 5#u8) r))
theorem step_eq (iter : Iter) (b : Back) (offset i : Usize) :
    step (iter,b,offset,i) = body idx val 1#usize nodes 1#u32 none iter b offset i := rfl
#print axioms step_eq
theorem step0 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 0#usize) b 0#usize 0#usize = ok (.cont (it 1#usize,fun r => b (restore 0 (node 5#u8) r),0#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 0#usize 1#usize 1#usize rfl]
  rfl
#print axioms step0
theorem step1 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 1#usize) b 0#usize 1#usize = ok (.cont (it 2#usize,fun r => b (restore 1 (node 2#u8) r),32#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 1#usize 1#usize 2#usize rfl]
  rw [add_eq 0#usize 32#usize 32#usize rfl]
  simp only [bind_tc_ok]
  unfold nodes
  rw [SDY_Slice.read 2#u8 0#usize 32#usize (by decide) (by decide) rfl]
  rfl
#print axioms step1
theorem step2 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 2#usize) b 32#usize 1#usize = ok (.cont (it 3#usize,fun r => b (restore 2 (node 2#u8) r),64#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 2#usize 1#usize 3#usize rfl]
  rw [add_eq 32#usize 32#usize 64#usize rfl]
  simp only [bind_tc_ok]
  unfold nodes
  rw [SDY_Slice.read 2#u8 32#usize 64#usize (by decide) (by decide) rfl]
  rfl
#print axioms step2
theorem step3 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 3#usize) b 64#usize 1#usize = ok (.cont (it 4#usize,fun r => b (restore 3 (node 2#u8) r),96#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 3#usize 1#usize 4#usize rfl]
  rw [add_eq 64#usize 32#usize 96#usize rfl]
  simp only [bind_tc_ok]
  unfold nodes
  rw [SDY_Slice.read 2#u8 64#usize 96#usize (by decide) (by decide) rfl]
  rfl
#print axioms step3
theorem step4 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 4#usize) b 96#usize 1#usize = ok (.cont (it 5#usize,fun r => b (restore 4 (node 2#u8) r),128#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 4#usize 1#usize 5#usize rfl]
  rw [add_eq 96#usize 32#usize 128#usize rfl]
  simp only [bind_tc_ok]
  unfold nodes
  rw [SDY_Slice.read 2#u8 96#usize 128#usize (by decide) (by decide) rfl]
  rfl
#print axioms step4
theorem step5 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 5#usize) b 128#usize 1#usize = ok (.cont (it 6#usize,fun r => b (restore 5 (node 2#u8) r),160#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 5#usize 1#usize 6#usize rfl]
  rw [add_eq 128#usize 32#usize 160#usize rfl]
  simp only [bind_tc_ok]
  unfold nodes
  rw [SDY_Slice.read 2#u8 128#usize 160#usize (by decide) (by decide) rfl]
  rfl
#print axioms step5
theorem step6 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 6#usize) b 160#usize 1#usize = ok (.cont (it 7#usize,fun r => b (restore 6 (node 2#u8) r),192#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 6#usize 1#usize 7#usize rfl]
  rw [add_eq 160#usize 32#usize 192#usize rfl]
  simp only [bind_tc_ok]
  unfold nodes
  rw [SDY_Slice.read 2#u8 160#usize 192#usize (by decide) (by decide) rfl]
  rfl
#print axioms step6
theorem step7 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 7#usize) b 192#usize 1#usize = ok (.cont (it 8#usize,fun r => b (restore 7 (node 2#u8) r),224#usize,1#usize)) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  rw [add_eq 7#usize 1#usize 8#usize rfl]
  rw [add_eq 192#usize 32#usize 224#usize rfl]
  simp only [bind_tc_ok]
  unfold nodes
  rw [SDY_Slice.read 2#u8 192#usize 224#usize (by decide) (by decide) rfl]
  rfl
#print axioms step7
theorem step8 (b : Back) : body idx val 1#usize nodes 1#u32 none (it 8#usize) b 224#usize 1#usize = ok (.done (224#usize,1#usize,none,b (it 8#usize))) := by
  unfold body multiproof.verify_in_place_loop0_loop0_loop0.body
  simp [SDY_Join_enumerateNext,core.slice.iter.IteratorIterMut.next,it,children,node]
  skip
#print axioms step8
theorem run8 (b : Back) : loop step (it 8#usize,b,224#usize,1#usize) = ok (224#usize,1#usize,none,fin8 b (it 8#usize)) := by
  exact SDY_Loop.done step _ _ ((step_eq (it 8#usize) b 224#usize 1#usize).trans (step8 b))
#print axioms run8
theorem run7 (b : Back) : loop step (it 7#usize,b,192#usize,1#usize) = ok (224#usize,1#usize,none,fin7 b (it 8#usize)) := by
  exact SDY_Loop.next step _ _ _ ((step_eq (it 7#usize) b 192#usize 1#usize).trans (step7 b)) (run8 _)
#print axioms run7
theorem run6 (b : Back) : loop step (it 6#usize,b,160#usize,1#usize) = ok (224#usize,1#usize,none,fin6 b (it 8#usize)) := by
  exact SDY_Loop.next step _ _ _ ((step_eq (it 6#usize) b 160#usize 1#usize).trans (step6 b)) (run7 _)
#print axioms run6
theorem run5 (b : Back) : loop step (it 5#usize,b,128#usize,1#usize) = ok (224#usize,1#usize,none,fin5 b (it 8#usize)) := by
  exact SDY_Loop.next step _ _ _ ((step_eq (it 5#usize) b 128#usize 1#usize).trans (step5 b)) (run6 _)
#print axioms run5
theorem run4 (b : Back) : loop step (it 4#usize,b,96#usize,1#usize) = ok (224#usize,1#usize,none,fin4 b (it 8#usize)) := by
  exact SDY_Loop.next step _ _ _ ((step_eq (it 4#usize) b 96#usize 1#usize).trans (step4 b)) (run5 _)
#print axioms run4
theorem run3 (b : Back) : loop step (it 3#usize,b,64#usize,1#usize) = ok (224#usize,1#usize,none,fin3 b (it 8#usize)) := by
  exact SDY_Loop.next step _ _ _ ((step_eq (it 3#usize) b 64#usize 1#usize).trans (step3 b)) (run4 _)
#print axioms run3
theorem run2 (b : Back) : loop step (it 2#usize,b,32#usize,1#usize) = ok (224#usize,1#usize,none,fin2 b (it 8#usize)) := by
  exact SDY_Loop.next step _ _ _ ((step_eq (it 2#usize) b 32#usize 1#usize).trans (step2 b)) (run3 _)
#print axioms run2
theorem run1 (b : Back) : loop step (it 1#usize,b,0#usize,1#usize) = ok (224#usize,1#usize,none,fin1 b (it 8#usize)) := by
  exact SDY_Loop.next step _ _ _ ((step_eq (it 1#usize) b 0#usize 1#usize).trans (step1 b)) (run2 _)
#print axioms run1
theorem run0 (b : Back) : loop step (it 0#usize,b,0#usize,0#usize) = ok (224#usize,1#usize,none,fin0 b (it 8#usize)) := by
  exact SDY_Loop.next step _ _ _ ((step_eq (it 0#usize) b 0#usize 0#usize).trans (step0 b)) (run1 _)
#print axioms run0
theorem inner : multiproof.verify_in_place_loop0_loop0_loop0 (it 0#usize) id idx val 1#usize nodes 0#usize 0#usize 1#u32 none = ok (224#usize,1#usize,none,fin0 id (it 8#usize)) := run0 id
#print axioms inner
end SDY_MpA
