import NJU_CommonObserved
import NLL_State
set_option autoImplicit false
noncomputable section
namespace NLP_EffectOrder
/-- Expansion is occurrence-indexed: repeated calls retain order and
multiplicity. This algebra alone provides no native child history. -/
def expand {E F : Type} (part : E → List F) (events : List E) : List F := events.flatMap part
theorem append {E F : Type} (part : E → List F) (before after : List E) :
 expand part (before++after)=expand part before++expand part after := by
 exact List.flatMap_append
theorem prefix_frame {E F : Type} (part : E → List F) (before : List E) (current : E)
 (observed : List F) (rest : List F) (localPrefix : part current=observed++rest) :
 ∃ suffix,expand part (before++[current])=(expand part before++observed)++suffix := by
 refine ⟨rest,?_⟩
 rw [append]
 simp only [expand,List.flatMap_cons,List.flatMap_nil,List.append_nil,localPrefix,List.append_assoc]
/-- Pointwise SAME-occurrence native-to-G laws compose in forward order.
The producer must instantiate each law internally; no free row premise. -/
theorem congr {E F : Type} (native source : E → List F) (events : List E)
 (stepEq : ∀ e∈events,native e=source e) : expand native events=expand source events := by
 induction events with
 | nil => rfl
 | cons e rest ih =>
   change native e++expand native rest=source e++expand source rest
   rw [stepEq e (by simp),ih (fun x member=>stepEq x (List.mem_cons_of_mem _ member))]
set_option pp.proofs false
#print append
#print prefix_frame
#print congr
#print axioms append
#print axioms prefix_frame
#print axioms congr
end NLP_EffectOrder
