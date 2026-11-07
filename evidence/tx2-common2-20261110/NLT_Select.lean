import NKE_Free
set_option autoImplicit false
namespace NLT_Select
/-- First actual occurrence, with no default success event inserted in history. -/
def pick {R A : Type} (value : R → Option A) : List R → Option A
 | [] => none
 | r::rs => match value r with | some x=>some x | none=>pick value rs
/-- Strict source order discharges selection consistency. This is a generic
finite-list lemma, not a parent certificate or a new trust item. -/
theorem unique {R A : Type} (key : R → Nat) (value : R → Option A) (site : Nat)
 (atSite : ∀ r x,value r=some x → key r=site)
 (records : List R) (ordered : records.Pairwise (fun a b=>key a<key b))
 (r : R) (member : r∈records) (x : A) (selected : value r=some x) :
 pick value records=some x := by
 induction records with
 | nil => simp at member
 | cons head rest ih =>
   obtain ⟨before,tail⟩:=List.pairwise_cons.mp ordered
   rcases List.mem_cons.mp member with equal|member
   · subst r
     simp only [pick,selected]
   · cases hv : value head with
     | none =>
       simp only [pick,hv]
       exact ih tail member
     | some y =>
       have h1:=atSite head y hv
       have h2:=atSite r x selected
       have h3:=before r member
       omega
#print axioms unique
end NLT_Select
