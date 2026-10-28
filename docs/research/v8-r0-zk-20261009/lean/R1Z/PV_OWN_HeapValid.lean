import R1Z.PV_OWN_Heap
set_option autoImplicit false
namespace R1Z.PV_OWN_HeapValid
open PV_OWN_Heap
/-- Freshness uses the size of each actual old live allocation. -/
theorem install (heap : Heap) (p : Nat) (c : Cell) (valid:Valid heap)
 (nonnull:p≠0) (positive:c.alignment>0) (aligned:p%c.alignment=0)
 (fresh:∀ q old, heap q=some old → old.live=true → q≠p → Disjoint p c q old) :
 Valid (put heap p (some c)) := by
 constructor
 · intro q a ha hl
   by_cases hq:q=p
   · subst q
     rw [put_same] at ha
     cases ha
     exact ⟨nonnull,positive,aligned⟩
   · rw [put_other _ _ _ _ hq] at ha
     exact valid.1 q a ha hl
 · intro q r a b ha hb la lb ne
   by_cases hq:q=p
   · subst q
     rw [put_same] at ha
     cases ha
     have hr:r≠p := Ne.symm ne
     rw [put_other _ _ _ _ hr] at hb
     exact fresh r b hb lb hr
   · rw [put_other _ _ _ _ hq] at ha
     by_cases hr:r=p
     · subst r
       rw [put_same] at hb
       cases hb
       exact Or.symm (fresh q a ha la hq)
     · rw [put_other _ _ _ _ hr] at hb
       exact valid.2 q r a b ha hb la lb ne
#print axioms install
end R1Z.PV_OWN_HeapValid
