import NLL_Prefix
set_option autoImplicit false
noncomputable section
namespace NLL_AppendPrefix
open Aeneas Aeneas.Std NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem prior (before log answered : NLL.History) (parts : Slice (Slice U8))
 (known : NLL_Prefix.At log answered parts) :
 NLL_Prefix.At (before++log) (before++answered) parts := by
 induction before with
 | nil => exact known
 | cons h t ih => exact NLL_Prefix.cons h _ _ _ ih

/-- A pending request lies inside the first segment. Counterfactual ideal
suffixes do not alter this prefix and are never native emitted events. -/
theorem suffix (log answered tail : NLL.History) (parts : Slice (Slice U8))
 (known : NLL_Prefix.At log answered parts) : NLL_Prefix.At (log++tail) answered parts := by
 have bound : answered.length<log.length := by
   by_contra bad
   have last:=known.2
   rw [List.getElem?_eq_none (by omega)] at last
   cases last
 constructor
 · rw [List.take_append_of_le_length (by omega)]
   exact known.1
 · rw [List.getElem?_append_left bound]
   exact known.2

#print axioms prior
#print axioms suffix
end NLL_AppendPrefix
end
