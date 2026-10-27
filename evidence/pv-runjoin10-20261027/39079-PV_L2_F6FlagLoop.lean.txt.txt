import R1Z.PV_L2_RecordBind

/-! Resource-justified instrumentation for the extracted flag/index loops.
The per-callee equations are proved against source, never accepted as new
runtime premises. Fuel is the actual remaining index distance. -/
set_option autoImplicit false
namespace R1Z.PV_L2_F6FlagLoop
open Aeneas Aeneas.Std Result R1Z.PV_L2_Record R1Z.CertCheck

def loop (site : Nat) (step : Bool → Usize → Recorded (Bool × Usize)) (bound : Usize) :
    Nat → Bool → Usize → Recorded Bool
  | 0,flag,index => if index < bound then ⟨.div,[.guard site index.val bound.val true]⟩
    else ⟨ok flag,[.guard site index.val bound.val false]⟩
  | fuel+1,flag,index => if index < bound then do
      let _ ← operation (.guard site index.val bound.val true) (ok ())
      let (flag1,index1) ← step flag index
      loop site step bound fuel flag1 index1
    else ⟨ok flag,[.guard site index.val bound.val false]⟩

theorem erases (site : Nat) (step : Bool → Usize → Recorded (Bool × Usize))
    (bound : Usize) (source : Bool → Usize → Result Bool)
    (unroll : ∀ flag index, source flag index = if index < bound then (do
      let (flag1,index1) ← (step flag index).value
      source flag1 index1) else ok flag)
    (progress : ∀ flag index after, (step flag index).value = ok after →
      after.2.val = index.val+1)
    (fuel : Nat) (flag : Bool) (index : Usize) (enough : bound.val ≤ index.val+fuel) :
    (loop site step bound fuel flag index).value = source flag index := by
  induction fuel generalizing flag index with
  | zero =>
    have hn : ¬index<bound := by rw [UScalar.lt_equiv];omega
    rw [loop,if_neg hn,unroll,if_neg hn]
  | succ fuel ih =>
    rw [loop,unroll]
    by_cases hn : index<bound
    · rw [if_pos hn,if_pos hn]
      simp only [operation_bind_value,bind_tc_ok]
      change (PV_L2_Record.bind (step flag index)
        (fun pair => loop site step bound fuel pair.1 pair.2)).value = _
      rw [bind_value]
      cases hs : (step flag index).value with
      | fail error => rfl
      | div => rfl
      | ok pair =>
        simp only [bind_tc_ok]
        exact ih pair.1 pair.2 (by have := progress flag index pair hs;omega)
    · rw [if_neg hn,if_neg hn]

#print axioms erases
end R1Z.PV_L2_F6FlagLoop
