import NJU_CommonObserved
import NLL_State
set_option autoImplicit false
noncomputable section
namespace NLP_EffectOrder
/-- Expansion is occurrence-indexed: repeated calls retain order and
multiplicity. This algebra alone provides no native child history. -/
def expand {E F : Type} (at : E → List F) (events : List E) : List F := events.flatMap at
theorem append {E F : Type} (at : E → List F) (before after : List E) :
 expand at (before++after)=expand at before++expand at after := by
 exact List.flatMap_append
theorem prefix {E F : Type} (at : E → List F) (before : List E) (current : E)
 (observed : List F) (rest : List F) (localPrefix : at current=observed++rest) :
 ∃ suffix,expand at (before++[current])=(expand at before++observed)++suffix := by
 refine ⟨rest,?_⟩
 rw [append]
 simp only [expand,List.flatMap_cons,List.flatMap_nil,List.append_nil,localPrefix,List.append_assoc]
/-- Pointwise SAME-occurrence native-to-G laws compose in forward order.
The producer must instantiate each law internally; no free row premise. -/
theorem congr {E F : Type} (native source : E → List F) (events : List E)
 (local : ∀ e∈events,native e=source e) : expand native events=expand source events := by
 induction events with
 | nil => rfl
 | cons e rest ih =>
   change native e++expand native rest=source e++expand source rest
   rw [local e (by simp),ih (fun x member=>local x (List.mem_cons_of_mem _ member))]
set_option pp.proofs false
#print append
#print prefix
#print congr
#print axioms append
#print axioms prefix
#print axioms congr
end NLP_EffectOrder
