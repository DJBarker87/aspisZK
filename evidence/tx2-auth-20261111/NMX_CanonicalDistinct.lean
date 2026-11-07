import NMX_KeyCarrier
set_option autoImplicit false
namespace NMX_CanonicalDistinct
open RSL
/-- The canonical helper's value is exactly key uniqueness, independent of
scan order. This is a symbolic list lemma, not a large enumeration. -/
theorem keys (accounts : List OwnedAccount) :
 distinctKeys accounts = true ↔ (accounts.map OwnedAccount.key).Nodup := by
 induction accounts with
 | nil => simp [distinctKeys]
 | cons a rest ih =>
   simp only [distinctKeys,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq,
    List.map_cons,List.nodup_cons,ih]
   constructor
   · intro h
     constructor
     · intro member
       obtain ⟨other,mem,same⟩ := List.mem_map.mp member
       exact h.1 other mem same
     · exact h.2
   · intro h
     constructor
     · intro other member same
       exact h.1 (List.mem_map.mpr ⟨other,member,same⟩)
     · exact h.2
#print axioms keys
end NMX_CanonicalDistinct
