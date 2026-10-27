import SDY_AddCStep
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace SDY_AddC
open SDY_Join_Release
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
  exact SDY_Loop.next step _ _ _ (wrapped0 b) (run1 _)
#print axioms run0

theorem emitted : sampler.add_small_base_p input 2147483647#u32 = ok (false,output) := by
  unfold sampler.add_small_base_p SDY_Join_intoIter
  simp only [bind_tc_ok]
  change (do let (c,b) ← loop step (it 0,id,2147483647#u32); ok (c != 0#u32,Array.from_slice input (b (it 0)).slice)) = _
  rw [run0]
  rfl
#print axioms emitted
end SDY_AddC
