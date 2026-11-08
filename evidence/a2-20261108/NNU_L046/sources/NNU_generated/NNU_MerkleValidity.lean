import NNU_MerkleLevels
import NNU_OffsetSubtract
set_option autoImplicit false
namespace AspisR1.NNU_MerkleValidity
open Aeneas Aeneas.Std Result MultiproofConeRef

theorem indices (idx : Array U32 16#usize) (n : Usize) (bounded : n.val≤16)
 (canonical : ∀ j, j<n.val → idx.val[j]!.val<262144)
 (ordered : ∀ a b, a<b → b<n.val → idx.val[a]!.val<idx.val[b]!.val)
 (fuel : Nat) (i : Usize) (enough : n.val-i.val≤fuel) :
 reference.valid_indices idx n i=.ok true := by
 induction fuel generalizing i with
 | zero =>
   have stop : i≥n := by change i.val≥n.val; omega
   rw [reference.valid_indices]
   simp only [stop,if_true]
 | succ fuel ih =>
   rw [reference.valid_indices]
   by_cases stop : i≥n
   · simp only [stop,if_true]
   · have active : i.val<n.val := by change ¬ i.val≥n.val at stop; omega
     have read := MultiproofConePhysicalPrelude.array_read idx i (by omega)
     have small : ¬ idx.val[i.val]! ≥ 262144#u32 := by
       change ¬ idx.val[i.val]!.val≥262144
       have := canonical i.val active
       omega
     have next_bound : i.val+1≤Usize.max := by scalar_tac
     let ni := Usize.ofNat (i.val+1) next_bound
     have add : (i+1#usize : Result Usize)=.ok ni :=
       NNU_OffsetArithmetic.add _ _ _ (by rfl)
     simp only [stop,if_false,read,bind_tc_ok,small]
     by_cases positive : i>0#usize
     · have sub_bound : i.val-1≤Usize.max := by scalar_tac
       let pi := Usize.ofNat (i.val-1) sub_bound
       have sub : (i-1#usize : Result Usize)=.ok pi :=
         NNU_OffsetSubtract.sub _ _ _ (by change 1≤i.val;change i.val>0 at positive;omega) (by rfl)
       have prior : pi.val<i.val := by change i.val>0 at positive;change i.val-1<i.val;omega
       have asc : ¬idx.val[pi.val]!≥idx.val[i.val]! := by
         change ¬ idx.val[pi.val]!.val≥idx.val[i.val]!.val
         have := ordered pi.val i.val prior active
         omega
       simp only [positive,if_true,sub,bind_tc_ok,
         MultiproofConePhysicalPrelude.array_read idx pi (by change i.val-1<16;omega),asc,if_false,add]
       exact ih ni (by change n.val-(i.val+1)≤fuel;omega)
     · simp only [positive,if_false,add,bind_tc_ok]
       exact ih ni (by change n.val-(i.val+1)≤fuel;omega)
#print axioms indices
end AspisR1.NNU_MerkleValidity
