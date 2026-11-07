import NNG_LegacyCalls136
import NNG_Array136
set_option autoImplicit false
namespace AspisR1.NNG_LegacyArrays136
open Aeneas Aeneas.Std Result NNG_Array136
open NMT_Transport (arr)

theorem index_map {A B : Type} {n : Usize} (f : A → B) (a : Array A n) (i : Usize) (bound : i.val<n.val) :
 Array.index_usize (arr f a) i=.ok (f (get a i bound)) := by
 rw [NNG_Array136.index _ i bound]
 simp only [NNG_Array136.get,arr,List.getElem_map]

theorem returned {A B : Type} {n : Usize} (f : A → B) (a : Array A n) (i : Usize) (bound : i.val<n.val)
 (value : A) (native : Array.index_usize a i=.ok value) :
 Array.index_usize (arr f a) i=.ok (f value) := by
 have same := Result.ok.inj ((NNG_Array136.index a i bound).symm.trans native)
 rw [index_map f a i bound,same]
#print axioms index_map
#print axioms returned
end AspisR1.NNG_LegacyArrays136
