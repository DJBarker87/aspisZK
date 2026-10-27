import FJo_QueryInjective
import FJl_PackedInjective
import FJl_PackedInitial
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJo_PackedLeaves
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortStoredDecisionDraftC4
/-- Accepted sampler injectivity resolves both initial maps, without recovery inputs. -/
theorem value (parsed : Parsed) (q : Fin 22 → Fin 262144)
    (tr : RawCutTranscriptRun.ErasedPrefix) (read : queries tr=some q) (j : Fin 22) :
    packed parsed q 0 (q j).val=some ((opening parsed j.val).take 480) ∧
    packed parsed q 1 (q j).val=some (slice (opening parsed j.val) 480 128) := by
  have injective := FJo_QueryInjective.value tr q read
  have indices (kind : Nat) (hk : kind≠2) : Function.Injective (fun l : Fin 22=>index q kind l.val) := by
    intro a b same
    have amod : (⟨a.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22)=a := Fin.ext (Nat.mod_eq_of_lt a.isLt)
    have bmod : (⟨b.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22)=b := Fin.ext (Nat.mod_eq_of_lt b.isLt)
    apply injective
    apply Fin.ext
    simpa only [index,amod,bmod,if_neg hk] using same
  have modj : (⟨j.val%22,Nat.mod_lt _ (by decide)⟩ : Fin 22)=j := Fin.ext (Nat.mod_eq_of_lt j.isLt)
  have c1 := FJl_PackedInjective.value parsed q 0 (indices 0 (by decide)) j
  have c2 := FJl_PackedInjective.value parsed q 1 (indices 1 (by decide)) j
  simpa only [index,modj,show (0:Nat)≠2 by decide,show (1:Nat)≠2 by decide,
    if_false,OraclePortPackedChoiceC4.payload,ite_true,show (1:Nat)≠0 by decide] using And.intro c1 c2
#print axioms value
end AspisR1.FJo_PackedLeaves
end
