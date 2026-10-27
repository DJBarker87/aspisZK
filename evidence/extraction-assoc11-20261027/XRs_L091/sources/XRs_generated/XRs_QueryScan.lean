import XRs_ClosedCallbacks
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRs_QueryScan
open AspisV8R19.Q22WordScan

def observe (s : List U32 × Nat × Bool) : ScanState × Bool :=
 (⟨s.1.map UScalar.val,s.2.1⟩,s.2.2)

theorem mem_val (xs : List U32) (x : U32) : x.val ∈ xs.map UScalar.val ↔ x ∈ xs := by
 constructor
 · intro h
   obtain ⟨y,hy,he⟩ := List.mem_map.mp h
   exact UScalar.eq_of_val_eq he ▸ hy
 · intro h
   exact List.mem_map.mpr ⟨x,h,rfl⟩

theorem stopped (xs words : List U32) (d : Nat) :
 words.foldl XRn_Join_scanWord (xs,d,true) = (xs,d,true) := by
 induction words with
 | nil => rfl
 | cons x words ih => simpa only [List.foldl_cons,XRn_Join_scanWord] using ih

theorem scan (xs words : List U32) (d : Nat) :
 observe (words.foldl XRn_Join_scanWord (xs,d,false)) =
 AspisV8R19.Q22WordScan.scan ⟨xs.map UScalar.val,d⟩ (words.map UScalar.val) := by
 induction words generalizing xs d with
 | nil => rfl
 | cons x words ih =>
   by_cases h : xs.length=22 ∨ d=64
   · simp only [List.foldl_cons,XRn_Join_scanWord,h,ite_true,ite_false,stopped,
       observe,List.map_cons,AspisV8R19.Q22WordScan.scan,List.length_map]
   · simp only [List.foldl_cons,XRn_Join_scanWord,h,ite_true,ite_false,
       List.map_cons,AspisV8R19.Q22WordScan.scan,List.length_map]
     rw [ih]
     unfold keep
     by_cases hm : x ∈ xs
     · simp only [hm,if_pos,mem_val]
     · simp only [hm,if_neg,mem_val,List.map_append,List.map_cons,List.map_nil]
#print axioms mem_val
#print axioms stopped
#print axioms scan
end XRs_QueryScan
