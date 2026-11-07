import LIBB_Tx2EnvCode
set_option autoImplicit false
noncomputable section
namespace LIBB_ReturnTrace
open Aeneas Aeneas.Std VTop_Stages NJU_CommonObserved
/-- A returned parent cannot contain a failed Merkle child. -/
def Safe {A : Type} (m : NJU_Log.Run Event A) : Prop :=
 ∀ a, m.result=.ok a → ∀ pr p folded err, Event.merkle pr p folded (.fail err) ∉ m.events

theorem bind {A B : Type} (m : NJU_Log.Run Event A) (k : A → NJU_Log.Run Event B)
 (hm : Safe m) (hk : ∀ a, Safe (k a)) : Safe (m >>= k) := by
 intro b returned pr p folded err
 cases h : m.result with
 | fail e => simp only [NJU_Log.erase_bind,h,Result.bind] at returned; cases returned
 | div => simp only [NJU_Log.erase_bind,h,Result.bind] at returned; cases returned
 | ok a =>
  change (NJU_Log.bind m k).result=_ at returned
  simp only [NJU_Log.bind,h] at returned
  change Event.merkle pr p folded (.fail err) ∉ (NJU_Log.bind m k).events
  simp only [NJU_Log.bind,h,List.mem_append,not_or]
  exact ⟨hm a h pr p folded err,hk a b returned pr p folded err⟩

theorem lift {A : Type} (call : Result A) : Safe (monadLift call : NJU_Log.Run Event A) := by
 intro a h pr p folded err
 exact List.not_mem_nil

theorem pure {A : Type} (a : A) : Safe (Pure.pure a : NJU_Log.Run Event A) := by
 intro a h pr p folded err
 exact List.not_mem_nil

theorem record {A : Type} (e : Result A → Event) (call : Result A)
 (valid : ∀ a pr p folded err, e (.ok a) ≠ Event.merkle pr p folded (.fail err)) :
 Safe (NJU_Log.record e call) := by
 intro a h pr p folded err
 change call=.ok a at h
 change Event.merkle pr p folded (.fail err) ∉ [e call]
 rw [h]
 simp only [List.mem_singleton]
 exact Ne.symm (valid a pr p folded err)

#print axioms bind
#print axioms lift
#print axioms pure
#print axioms record
end LIBB_ReturnTrace
end
