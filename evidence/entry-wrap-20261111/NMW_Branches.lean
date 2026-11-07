import NMW_Symbolic
import Hiq_DispatchFirst
import Hiq_DispatchSecond
import Hiq_DispatchAdmitted
set_option autoImplicit false
noncomputable section
namespace NMW_Branches
open Aeneas Aeneas.Std Result AspisR1 NMW_Symbolic
/-- Universal child result: no success, endpoint, or buffer premise. -/
theorem first {A V : Type} (ops : Ops A V) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (domain : Hiq_ReleaseRoute.stage1 d) :
 process ops p a d = ops.first p a d := by
 classical
 rcases domain with h | h
 all_goals simp [Array.make,process,Hiq_DispatchSource.firstByte,
   Hiq_DispatchSource.copied,h,Hiq_DispatchSource.eqU8]
 all_goals rfl

theorem second {A V : Type} (ops : Ops A V) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (domain : Hiq_ReleaseRoute.asq8 d) :
 process ops p a d = ops.second p a d := by
 classical
 have head := Hiq_RouteHead.second_head d domain
 have no := Hiq_DispatchSecond.disjoint d domain
 have no10 : d.val ≠ [3#u8,10#u8] := fun h => no (Or.inl h)
 have no11 : d.val ≠ [3#u8,11#u8] := fun h => no (Or.inr h)
 simp only [process,Hiq_DispatchSource.firstByte,head,Hiq_DispatchSource.copied,bind_tc_ok]
 change (do
   let b ← Hiq_DispatchSource.eqU8 d (Array.make 2#usize [3#u8,10#u8])
   if b then ops.first p a d else do
     let b1 ← Hiq_DispatchSource.eqU8 d (Array.make 2#usize [3#u8,11#u8])
     if b1 then ops.first p a d else ops.second p a d) = ops.second p a d
 simp [Hiq_DispatchSource.eqU8,Array.make,no10,no11]

theorem entry_total {A V : Type} (ops : Ops A V) (reject : V)
 (p : Hiq_DispatchSource.Key) (a : Slice A) (d : Slice U8) :
 entry ops reject p a d = match Hiq_ReleaseRoute.route d with
 | .first => ops.first p a d
 | .second => ops.second p a d
 | .reject => ok reject := by
 classical
 rw [entry,Hiq_DispatchAdmitted.exact]
 by_cases one : Hiq_ReleaseRoute.stage1 d
 · rw [first ops p a d one]
   simp [Hiq_ReleaseRoute.route,one]
 by_cases two : Hiq_ReleaseRoute.asq8 d
 · rw [second ops p a d two]
   simp [Hiq_ReleaseRoute.route,one,two]
 · simp [Hiq_ReleaseRoute.route,one,two]
#print axioms first
#print axioms second
#print axioms entry_total
end NMW_Branches
end
