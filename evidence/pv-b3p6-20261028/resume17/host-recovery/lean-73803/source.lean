import PV_B3P_DirectRange17227
import PV_B3P_NativeDigestStore15227
namespace PV_B3P_227
open Aeneas Aeneas.Std Result ControlFlow Error
set_option autoImplicit false
def host_terminal.lift_m31
  (value : aspis_core.field.M31) : Result aspis_core.field.QM31 := do
  let c ← aspis_core.field.CM31.from_m31 value
  aspis_core.field.QM31.from_cm31 c

def host_terminal.add_digest_binding_loop.body
  (i : Std.Usize) (selector : aspis_core.field.QM31)
  (opened : Array aspis_core.field.QM31 16#usize) (start : Std.Usize)
  (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool)
  (iter : core.ops.range.Range Std.Usize)
  (output : Array aspis_core.field.QM31 8#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array
    aspis_core.field.QM31 8#usize)) (Array aspis_core.field.QM31 8#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done output)
  | some lane =>
    let target ← Array.index_usize expected lane
    let target1 ←
      if right_tweak
      then
        do
        let i1 ← lift (Std.Usize.wrapping_add lane 1#usize)
        if i1 = i
        then
          let m ← (Result.ok aspis_statement.poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK)
          aspis_core.field.M31.add target m
        else ok target
      else ok target
    let q ← Array.index_usize output lane
    let i1 ← lift (Std.Usize.wrapping_add start lane)
    let q1 ← Array.index_usize opened i1
    let q2 ← host_terminal.lift_m31 target1
    let q3 ← aspis_core.field.QM31.sub q1 q2
    let q4 ← aspis_core.field.QM31.mul selector q3
    let q5 ← aspis_core.field.QM31.add q q4
    let output1 ← Array.update output lane q5
    ok (cont (iter1, output1))

def host_terminal.add_digest_binding_loop
  (i : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (output : Array aspis_core.field.QM31 8#usize)
  (selector : aspis_core.field.QM31)
  (opened : Array aspis_core.field.QM31 16#usize) (start : Std.Usize)
  (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool) :
  Result (Array aspis_core.field.QM31 8#usize)
  := do
  loop
    (fun (iter1, output1) => host_terminal.add_digest_binding_loop.body i
      selector opened start expected right_tweak iter1 output1)
    (iter, output)

def host_terminal.add_digest_binding
  (output : Array aspis_core.field.QM31 8#usize)
  (selector : aspis_core.field.QM31)
  (opened : Array aspis_core.field.QM31 16#usize) (start : Std.Usize)
  (expected : Array aspis_core.field.M31 8#usize) (right_tweak : Bool) :
  Result (Array aspis_core.field.QM31 8#usize)
  := do
  let i ← (Result.ok aspis_statement.poseidon2.DIGEST_ELEMS)
  host_terminal.add_digest_binding_loop i { start := 0#usize, «end» := i }
    output selector opened start expected right_tweak
end PV_B3P_227
namespace PV_B3P_Direct17227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Binding9227 PV_B3P_Binding11227 PV_B3P_Binding13227 PV_B3P_Native15227 Result ControlFlow
set_option autoImplicit false
attribute [local irreducible] aspis_core.field.QM31.add aspis_core.field.QM31.mul aspis_core.field.QM31.sub aspis_core.field.M31.add Array.index_usize Array.update

theorem digest_body17 (selector : aspis_core.field.QM31)
    (opened : Array aspis_core.field.QM31 16#usize) (start : Usize)
    (expected : Array aspis_core.field.M31 8#usize) (tweak : Bool)
    (cursor : Usize) (output : Array aspis_core.field.QM31 8#usize) :
    host_terminal.add_digest_binding_loop.body 8#usize selector opened start expected tweak
      { start := cursor, «end» := 8#usize } output =
    if cursor < 8#usize then do
      let next ← digest_store_cell11 selector opened start expected tweak output cursor
      .ok (.cont ({ start := Usize.wrapping_add cursor 1#usize, «end» := 8#usize },next))
    else .ok (.done output) := by
  by_cases h : cursor < 8#usize
  · have inc := PV_B3P_Offset226V3.add_value cursor 1#usize (by scalar_tac)
    have edge : Usize.wrapping_add cursor 1#usize = 8#usize ↔ cursor = 7#usize := by scalar_tac
    by_cases last : cursor = 7#usize <;> cases tweak <;>
      simp only [host_terminal.add_digest_binding_loop.body,range_next_extraction17,h,
        if_true,if_false,bind_tc_ok,digest_store_cell11,reference_terminal.tweak227,
        host_terminal.lift_m31,reference_terminal.lift_m31,edge,last,
        Bool.false_eq_true,Bool.true_eq_true,PV_B3P_Ordered227.bind_assoc]
  · simp only [host_terminal.add_digest_binding_loop.body,range_next_extraction17,h,
      if_false,bind_tc_ok]

theorem digest_loop_plan17 (selector : aspis_core.field.QM31)
    (opened : Array aspis_core.field.QM31 16#usize) (start : Usize)
    (expected : Array aspis_core.field.M31 8#usize) (tweak : Bool)
    (n : Nat) (cursor : Usize) (output : Array aspis_core.field.QM31 8#usize)
    (bound : cursor.val+n=8) :
    host_terminal.add_digest_binding_loop 8#usize { start := cursor, «end» := 8#usize }
      output selector opened start expected tweak =
    usize_plan (digest_store_cell11 selector opened start expected tweak) n cursor output := by
  induction n generalizing cursor output with
  | zero =>
    have stop : ¬ cursor < 8#usize := by scalar_tac
    unfold host_terminal.add_digest_binding_loop
    rw [loop.eq_1]
    simp only [digest_body17,stop,if_false,bind_tc_ok,usize_plan]
  | succ n ih =>
    have inside : cursor < 8#usize := by scalar_tac
    have inc := PV_B3P_Offset226V3.add_value cursor 1#usize (by scalar_tac)
    have rest : (Usize.wrapping_add cursor 1#usize).val+n=8 := by omega
    unfold host_terminal.add_digest_binding_loop
    rw [loop.eq_1]
    simp only [digest_body17,inside,if_true,usize_plan,PV_B3P_Ordered227.bind_assoc]
    cases operation : digest_store_cell11 selector opened start expected tweak output cursor with
    | fail e => rfl
    | div => rfl
    | ok next =>
      simpa only [host_terminal.add_digest_binding_loop,bind_tc_ok,lift] using
        ih (Usize.wrapping_add cursor 1#usize) next rest

theorem digest_extraction_reference17 (output : Array aspis_core.field.QM31 8#usize)
    (selector : aspis_core.field.QM31) (opened : Array aspis_core.field.QM31 16#usize)
    (start : Usize) (expected : Array aspis_core.field.M31 8#usize) (tweak : Bool) :
    host_terminal.add_digest_binding output selector opened start expected tweak =
      reference_terminal.add_digest_binding output selector opened start expected tweak := by
  apply Eq.trans _ (native_digest_store_binding15 output selector opened start expected tweak)
  unfold host_terminal.add_digest_binding native_digest_store15
  simp only [aspis_statement.poseidon2.DIGEST_ELEMS,bind_tc_ok]
  rw [digest_loop_plan17 selector opened start expected tweak 8 0#usize output (by rfl),
    range_plan13 _ 0#usize 8#usize 8 output (by rfl)]
#print axioms digest_body17
#print axioms digest_loop_plan17
#print axioms digest_extraction_reference17
end PV_B3P_Direct17227
