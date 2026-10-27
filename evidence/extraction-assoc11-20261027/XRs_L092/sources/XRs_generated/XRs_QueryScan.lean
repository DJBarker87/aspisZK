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
 | cons x words ih => simpa [List.foldl_cons,XRn_Join_scanWord] using ih

theorem scan (xs words : List U32) (d : Nat) :
 observe (words.foldl XRn_Join_scanWord (xs,d,false)) =
 AspisV8R19.Q22WordScan.scan ⟨xs.map UScalar.val,d⟩ (words.map UScalar.val) := by
 induction words generalizing xs d with
 | nil => rfl
 | cons x words ih =>
   by_cases h : xs.length=22 ∨ d=64
   · simp [List.foldl_cons,XRn_Join_scanWord,h,stopped,
       observe,AspisV8R19.Q22WordScan.scan]
   · by_cases hm : x ∈ xs
     · simpa [List.foldl_cons,XRn_Join_scanWord,h,hm,
         AspisV8R19.Q22WordScan.scan,keep,mem_val] using ih xs (d+1)
     · simpa [List.foldl_cons,XRn_Join_scanWord,h,hm,
         AspisV8R19.Q22WordScan.scan,keep,mem_val] using ih (xs++[x]) (d+1)
#print axioms mem_val
#print axioms stopped
#print axioms scan
end XRs_QueryScan
