import R1Z.PV_Inv_GlobalSafety
set_option autoImplicit false
namespace R1Z.PV_Inv_GlobalPairs
open PV_Inv_RawSlots PV_Inv_GlobalSlots PV_Inv_GlobalSafety
variable {I V W L : Type} [DecidableEq I] [Zero W] [DecidableEq W]

def endpoints (producer consumer : L → I × Entry V W) (links : List L) : List (I × Entry V W) :=
  links.flatMap (fun link => [producer link,consumer link])

theorem safe_pairs (P : I → V → Prop) (producer consumer : L → I × Entry V W) (links : List L)
    (hp : ∀ l ∈ links, P (producer l).1 (producer l).2.value)
    (hc : ∀ l ∈ links, P (consumer l).1 (consumer l).2.value) :
    ∀ e ∈ endpoints producer consumer links, P e.1 e.2.value := by
  intro e he
  obtain ⟨l,hl,he⟩ := List.mem_flatMap.mp he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with he|he
  · subst e; exact hp l hl
  · subst e; exact hc l hl

theorem build_safe (P : I → V → Prop) (producer consumer : L → I × Entry V W) (links : List L)
    (hp : ∀ l ∈ links, P (producer l).1 (producer l).2.value)
    (hc : ∀ l ∈ links, P (consumer l).1 (consumer l).2.value)
    (z : V) (s : State I V W)
    (hr : PV_Inv_GlobalSlots.run (empty z) (endpoints producer consumer links)=some s) :
    PV_Inv_GlobalSlots.Good P s :=
  run_good P (empty z) s _ (empty_good z P) (safe_pairs P producer consumer links hp hc) hr

#print axioms safe_pairs
#print axioms build_safe
end R1Z.PV_Inv_GlobalPairs
