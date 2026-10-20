import AspisR1GeometryCandidate7.Funs
set_option autoImplicit false
namespace AspisR1.CuSavingsGeometryNode
open Aeneas Aeneas.Std Result ControlFlow AspisR1GeometryCandidate7
abbrev M := field.M31
abbrev Range := core.ops.range.Range I32

def step (node : M) : Result M := do
  let square ← field.M31.mul node node
  let doubled ← field.M31.double square
  field.M31.sub doubled field.M31.ONE

theorem next0 : core.iter.range.IteratorRange.next core.iter.range.StepI32
    ({start:=0#i32,«end»:=2#i32}:Range)=.ok (some 0#i32,{start:=1#i32,«end»:=2#i32}) := by rfl
theorem next1 : core.iter.range.IteratorRange.next core.iter.range.StepI32
    ({start:=1#i32,«end»:=2#i32}:Range)=.ok (some 1#i32,{start:=2#i32,«end»:=2#i32}) := by rfl
theorem next2 : core.iter.range.IteratorRange.next core.iter.range.StepI32
    ({start:=2#i32,«end»:=2#i32}:Range)=.ok (none,{start:=2#i32,«end»:=2#i32}) := by rfl

private theorem unroll {S T : Type} (b : S→Result (ControlFlow S T)) (s : S) :
    loop b s=(do let flow ← b s
                 match flow with | .done value => .ok value | .cont next => loop b next) := by
  rw [loop]
  cases b s with
  | fail error => rfl
  | div => rfl
  | ok value => cases value <;> rfl

theorem two_steps (node : M) :
    old.node_loop1 {start:=0#i32,«end»:=2#i32} node=(do let first ← step node;step first) := by
  unfold old.node_loop1
  rw [unroll]
  simp only [old.node_loop1.body,next0,bind_tc_ok,uncurry_apply_pair]
  unfold step
  simp only [bind_assoc_eq]
  apply (bind_eq_iff (field.M31.mul node node) _ _).mpr
  intro square _
  apply (bind_eq_iff (field.M31.double square) _ _).mpr
  intro doubled _
  apply (bind_eq_iff (field.M31.sub doubled field.M31.ONE) _ _).mpr
  intro first _
  simp only [bind_tc_ok,uncurry_apply_pair]
  rw [unroll]
  simp only [old.node_loop1.body,next1,bind_tc_ok,uncurry_apply_pair]
  simp only [bind_assoc_eq]
  apply (bind_eq_iff (field.M31.mul first first) _ _).mpr
  intro square1 _
  apply (bind_eq_iff (field.M31.double square1) _ _).mpr
  intro doubled1 _
  apply (bind_eq_iff (field.M31.sub doubled1 field.M31.ONE) _ _).mpr
  intro result _
  simp only [bind_tc_ok,uncurry_apply_pair]
  rw [unroll]
  simp only [old.node_loop1.body,next2,bind_tc_ok,uncurry_apply_pair]

#print axioms next0
#print axioms next1
#print axioms next2
#print axioms two_steps
end AspisR1.CuSavingsGeometryNode
