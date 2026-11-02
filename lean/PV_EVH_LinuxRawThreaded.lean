import PV_EVH_LinuxRawHistory
set_option autoImplicit false
noncomputable section
namespace PV_EVH_LinuxRawThreaded
open Aeneas Aeneas.Std ProverRwFull
open PV_EVH_LinuxRawControl (Reply)
open PV_EVH_LinuxRawHistory (execute Call)
open PV_EVH_World (World)

/-- Private pre/post buffers and OS worlds form one continuous execution.
No intermediate answer can be substituted independently of its next call. -/
def Threaded (a : Array U8 64#usize) (w : World) :
    List Call → Array U8 64#usize → World → Prop
  | [], b, v => b = a ∧ v = w
  | c :: cs, b, v => c.before = a ∧ c.worldBefore = w ∧
      Threaded c.after.buffer c.after.world cs b v

theorem continuous
    (syscall : Nat → Nat → Array U8 64#usize → World → Reply)
    (address fuel offset : Nat) (a : Array U8 64#usize) (w : World) :
    let e := execute syscall address fuel offset a w
    Threaded a w e.calls e.delivery.buffer e.delivery.world := by
  induction fuel generalizing offset a w with
  | zero => exact ⟨rfl,rfl⟩
  | succ fuel ih =>
    simp only [execute,Threaded,true_and]
    cases hr : (syscall (address+offset) (64-offset) a w).result with
    | fault e => simp only [hr,Threaded,and_self]
    | exhausted => simp only [hr,Threaded,and_self]
    | returned r =>
      cases r with
      | fail e => simp only [hr,Threaded,and_self]
      | div => simp only [hr,Threaded,and_self]
      | ok ret =>
        simp only [hr]
        split_ifs <;> first | exact ih _ _ _ | exact ⟨rfl,rfl⟩

#print axioms continuous
end PV_EVH_LinuxRawThreaded
