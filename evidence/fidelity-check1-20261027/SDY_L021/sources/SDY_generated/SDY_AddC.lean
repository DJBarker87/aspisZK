import SDY_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_AddC
open SDY_Join_Release
abbrev Iter := core.slice.iter.IterMut U32
abbrev Back := Iter → Iter
abbrev State := Iter × Back × U32
abbrev body := sampler.add_small_base_p_loop.body
def step (s : State) := body s.1 s.2.1 s.2.2
def input : Array U32 8#usize := ⟨[5#u32,5#u32,5#u32,5#u32,5#u32,5#u32,5#u32,5#u32],by simp⟩
def output : Array U32 8#usize := ⟨[5#u32,6#u32,5#u32,5#u32,5#u32,5#u32,5#u32,5#u32],by simp⟩
def it (i : Nat) : Iter := ⟨input.to_slice,i⟩
def restore (i : Nat) (x : U32) : Back := fun r => {r with slice := r.slice.setAtNat i x}
def fin8 (b : Back) : Back := b
def fin7 (b : Back) : Back := fin8 (fun r => b (restore 7 5#u32 r))
def fin6 (b : Back) : Back := fin7 (fun r => b (restore 6 5#u32 r))
def fin5 (b : Back) : Back := fin6 (fun r => b (restore 5 5#u32 r))
def fin4 (b : Back) : Back := fin5 (fun r => b (restore 4 5#u32 r))
def fin3 (b : Back) : Back := fin4 (fun r => b (restore 3 5#u32 r))
def fin2 (b : Back) : Back := fin3 (fun r => b (restore 2 5#u32 r))
def fin1 (b : Back) : Back := fin2 (fun r => b (restore 1 6#u32 r))
def fin0 (b : Back) : Back := fin1 (fun r => b (restore 0 5#u32 r))

theorem step0 (b : Back) : body (it 0) b 2147483647#u32 = ok (.cont (it 1,fun r => b (restore 0 5#u32 r),1#u32)) := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  rfl
#print axioms step0

theorem step1 (b : Back) : body (it 1) b 1#u32 = ok (.cont (it 2,fun r => b (restore 1 6#u32 r),0#u32)) := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  rfl
#print axioms step1

theorem step2 (b : Back) : body (it 2) b 0#u32 = ok (.cont (it 3,fun r => b (restore 2 5#u32 r),0#u32)) := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  rfl
#print axioms step2

theorem step3 (b : Back) : body (it 3) b 0#u32 = ok (.cont (it 4,fun r => b (restore 3 5#u32 r),0#u32)) := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  rfl
#print axioms step3

theorem step4 (b : Back) : body (it 4) b 0#u32 = ok (.cont (it 5,fun r => b (restore 4 5#u32 r),0#u32)) := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  rfl
#print axioms step4

theorem step5 (b : Back) : body (it 5) b 0#u32 = ok (.cont (it 6,fun r => b (restore 5 5#u32 r),0#u32)) := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  rfl
#print axioms step5

theorem step6 (b : Back) : body (it 6) b 0#u32 = ok (.cont (it 7,fun r => b (restore 6 5#u32 r),0#u32)) := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  rfl
#print axioms step6

theorem step7 (b : Back) : body (it 7) b 0#u32 = ok (.cont (it 8,fun r => b (restore 7 5#u32 r),0#u32)) := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  rfl
#print axioms step7

theorem step8 (b : Back) : body (it 8) b 0#u32 = ok (.done (0#u32,b)) := by
  unfold body sampler.add_small_base_p_loop.body
  simp [core.slice.iter.IteratorIterMut.next,it,input,restore,aspis_core.field.P]
  skip
#print axioms step8

theorem run8 (b : Back) : loop step (it 8,b,0#u32) = ok (0#u32,fin8 b) := by
  rw [loop.eq_def]
  change (match body (it 8) b 0#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step8]
  rfl
#print axioms run8

theorem run7 (b : Back) : loop step (it 7,b,0#u32) = ok (0#u32,fin7 b) := by
  rw [loop.eq_def]
  change (match body (it 7) b 0#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step7]
  exact run8 _
#print axioms run7

theorem run6 (b : Back) : loop step (it 6,b,0#u32) = ok (0#u32,fin6 b) := by
  rw [loop.eq_def]
  change (match body (it 6) b 0#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step6]
  exact run7 _
#print axioms run6

theorem run5 (b : Back) : loop step (it 5,b,0#u32) = ok (0#u32,fin5 b) := by
  rw [loop.eq_def]
  change (match body (it 5) b 0#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step5]
  exact run6 _
#print axioms run5

theorem run4 (b : Back) : loop step (it 4,b,0#u32) = ok (0#u32,fin4 b) := by
  rw [loop.eq_def]
  change (match body (it 4) b 0#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step4]
  exact run5 _
#print axioms run4

theorem run3 (b : Back) : loop step (it 3,b,0#u32) = ok (0#u32,fin3 b) := by
  rw [loop.eq_def]
  change (match body (it 3) b 0#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step3]
  exact run4 _
#print axioms run3

theorem run2 (b : Back) : loop step (it 2,b,0#u32) = ok (0#u32,fin2 b) := by
  rw [loop.eq_def]
  change (match body (it 2) b 0#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step2]
  exact run3 _
#print axioms run2

theorem run1 (b : Back) : loop step (it 1,b,1#u32) = ok (0#u32,fin1 b) := by
  rw [loop.eq_def]
  change (match body (it 1) b 1#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step1]
  exact run2 _
#print axioms run1

theorem run0 (b : Back) : loop step (it 0,b,2147483647#u32) = ok (0#u32,fin0 b) := by
  rw [loop.eq_def]
  change (match body (it 0) b 2147483647#u32 with
    | ok (.cont s) => loop step s
    | ok (.done v) => ok v
    | fail e => fail e
    | div => div) = _
  rw [step0]
  exact run1 _
#print axioms run0

theorem emitted : sampler.add_small_base_p input 2147483647#u32 = ok (false,output) := by
  unfold sampler.add_small_base_p SDY_Join_intoIter
  simp only [bind_tc_ok]
  change (do let (c,b) ← loop step (it 0,id,2147483647#u32); ok (c != 0#u32,Array.from_slice input (b (it 0)).slice)) = _
  rw [run0]
  rfl
#print axioms emitted
end SDY_AddC
