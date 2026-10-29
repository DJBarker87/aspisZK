import PV_L1F_ReturnedCount
import PV_RJ4IDB_Channels
set_option autoImplicit false
namespace PV_L1F_ReturnedPrefix
open Aeneas Aeneas.Std R1Z.ProverCommitRetry34 PV_RJ4IDB
/-- The source success continuation emits the field it just read. No count is
emitted by this continuation on stop, failure or divergence. Earlier emissions
remain in prefix, rather than being inferred from this returned value. -/
def suffix {P S : Type} (out : Result (Step (Published P) × S)) : List Event :=
 match PV_L1F_ReturnedCount.read out with
 | none => []
 | some n => [.attempts n]

theorem counts_suffix {P S : Type} (out : Result (Step (Published P) × S)) :
 counts (suffix out) = (PV_L1F_ReturnedCount.read out).toList := by
 unfold suffix
 cases PV_L1F_ReturnedCount.read out <;> rfl
#print axioms counts_suffix

theorem rejects_suffix {P S : Type} (out : Result (Step (Published P) × S)) :
 rejections (suffix out) = [] := by
 unfold suffix
 cases PV_L1F_ReturnedCount.read out <;> rfl
#print axioms rejects_suffix

theorem ordered_acquisition {P S : Type} (prefix : List Event)
 (out : Result (Step (Published P) × S)) :
 (counts (prefix++suffix out),rejections (prefix++suffix out)) =
 (counts prefix++(PV_L1F_ReturnedCount.read out).toList,rejections prefix) := by
 simp only [counts,rejections,List.filterMap_append]
 change (counts prefix++counts (suffix out),rejections prefix++rejections (suffix out)) = _
 rw [counts_suffix,rejects_suffix,List.append_nil]
#print axioms ordered_acquisition
end PV_L1F_ReturnedPrefix
