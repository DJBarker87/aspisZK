import NJL_WindowPowers
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_WindowPowerFrame
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
abbrev State := Fin 8 → NQ
def put (s : State) (i : Fin 8) (x : NQ) : State := fun j=>if j=i then x else s j
/-- NJB_K098/K099: save current power, then actual multiply; all8post cells,
returned next power, one call and next slot, under proved same domains. -/
def Cut (before after : State) (lambda power reply : NQ) (i : Fin 8) (calls next : Nat) : Prop :=
 Canon lambda ∧ Canon power ∧ Canon reply ∧ calls=1 ∧ next=i.val+1 ∧ after=put before i power
def run (lambda : NQ) : List (Fin 8) → State → NQ → Result (State × NQ)
 | [],s,power=>ok (s,power)
 | i::is,s,power=>do
  let next ← FIq_Native.field.QM31.mul power lambda
  run lambda is (put s i power) next
inductive Trace (lambda : NQ) : List (Fin 8) → State → NQ → State → NQ → Prop
 | nil (s : State) (p : NQ) : Trace lambda [] s p s p
 | cons {i is before middle power next last}
   (multiply : FIq_Native.field.QM31.mul power lambda=ok next)
   (cut : Cut before (put before i power) lambda power next i 1 (i.val+1))
   (rest : Trace lambda is (put before i power) next middle last) : Trace lambda (i::is) before power middle last
/-- Lift the actual power recurrence into EVERY mutable8cell native frame.
The recurrence trace is generic SUPPORT, instantiated internally by the root. -/
theorem lift (lambda : NQ) {n : Nat} {power next : NQ} {values : List NQ}
 (actual : NJL_WindowPowers.Trace lambda n power values next) (indices : List (Fin 8))
 (length : indices.length=n) (before : State) (hl : Canon lambda) (hp : Canon power) :
 ∃ after,run lambda indices before power=ok (after,next) ∧ Trace lambda indices before power after next ∧
 after=(indices.zip values).foldl (fun state entry=>put state entry.1 entry.2) before := by
 induction actual generalizing indices before with
 | nil power =>
  cases indices with
  | nil => exact ⟨before,rfl,.nil before power,rfl⟩
  | cons i is => simp at length
 | @cons n power middle values last multiply tail ih =>
  cases indices with
  | nil => simp at length
  | cons i is =>
   have hm := (FIv_NativeValue.mul power lambda middle hp hl multiply).1
   obtain ⟨after,call,trace,frame⟩ := ih is (by simpa only [List.length_cons,Nat.succ.injEq] using length) (put before i power) hm
   refine ⟨after,?_,.cons multiply ⟨hl,hp,hm,rfl,rfl,rfl⟩ trace,?_⟩
   · simp only [run,multiply,call,bind_tc_ok]
   · simpa only [List.zip_cons_cons,List.foldl_cons] using frame
#print lift
#print axioms lift
end AspisR1.NJL_WindowPowerFrame
end
