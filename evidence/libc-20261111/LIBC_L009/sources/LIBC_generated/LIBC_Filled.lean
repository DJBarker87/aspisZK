import LIB_Env
import NGC_ReferenceValues
set_option autoImplicit false
namespace LIBC_Filled
open Aeneas Aeneas.Std
open RSL
/-- Frozen TX1:064 caller clause: u8, identity Clone, n ≤ 32768. -/
def Domain (n : Nat) : Prop := n ≤ 32768
def value (n : Nat) (env : Env) : Except Unit Bytes :=
 if env.reservation then .ok (List.replicate n (0 : UInt8)) else .error ()
def child : Child Nat (Except Unit Bytes) :=
 LIB_Carriers.ofFn Domain value (fun _ _ => [])
theorem functional : Child.Functional child := LIB_Carriers.ofFn_functional _ _ _
theorem returns (n : Nat) (env : Env) :
 NND_Returned.Returns (child.law n) env (value n env) := LIB_Carriers.ofFn_returns _ _ _ n env
/-- SAME reservation reply; the complete CLOSED heap model includes Err. -/
theorem model (n : Usize) (env : Env) :
 AspisR1.OraclePortStdAllocation.filled n 0#u8 env.reservation =
 .ok (if env.reservation then .ok ⟨List.replicate n.val 0#u8,by
   simp only [List.length_replicate]; scalar_tac⟩ else .error .allocation) := by
 rw [AspisR1.OraclePortStdAllocation.filled_exact]
 cases env.reservation <;> rfl
/-- Byte carrier transport is independent of the allocation model. -/
theorem bytes (n : Usize) :
 LIB_Carriers.bytes (⟨List.replicate n.val 0#u8,by
   simp only [List.length_replicate]; scalar_tac⟩ : Slice U8) =
 List.replicate n.val (0 : UInt8) := by
 change List.map _ (List.replicate n.val 0#u8) = _
 rw [List.map_replicate]
 rfl
/-- The carrier port discards only the unobservable allocation-error payload. -/
def port (r : Except AspisR1.OraclePortStdAllocation.AllocationError (alloc.vec.Vec U8)) :
 Except Unit Bytes := match r with
 | .ok v => .ok (LIB_Carriers.bytes (alloc.vec.Vec.deref v))
 | .error _ => .error ()
/-- The complete source-model result equals the installed graph's value. -/
theorem model_port (n : Usize) (env : Env) :
 (do let r ← AspisR1.OraclePortStdAllocation.filled n 0#u8 env.reservation
     Result.ok (port r)) = Result.ok (value n.val env) := by
 rw [model]
 cases h : env.reservation
 · simp only [h,Bool.false_eq_true,if_false,Result.bind_tc_ok,port,value]
 · simp only [h,if_true,Result.bind_tc_ok,port,value]
   congr 2
   exact bytes n
theorem exact (n : Nat) (env : Env) (o : Obs (Except Unit Bytes)) :
 child.law n env o ↔ o = ⟨.ret (value n env), []⟩ := Iff.rfl

#print axioms functional
#print axioms returns
#print axioms model
#print axioms bytes
#print axioms model_port
#print axioms exact
end LIBC_Filled
