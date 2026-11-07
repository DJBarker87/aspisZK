import NNH_MerkleRowExecute
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_MerkleRowsExecute
open Aeneas Aeneas.Std NJP_RowModel NJP_LoopModel NJP_NativeRowCut
open NNH_MerkleRowExecute
attribute [local instance] Classical.propDecidable

def run (H : Request → Digest) (nodes : Nat → U8) (length : Nat) :
 Nat → Scratch → Nat → Nat → List (Request × Digest) × Level
 | 0,s,i,w => if s.n≤i then ([],.done {s with n:=w}) else ([],.stop s)
 | fuel+1,s,i,w =>
   if s.n≤i then ([],.done {s with n:=w}) else
   let log := capture H nodes length s i w
   let next := after H nodes length s i w
   if returned s i length then
    let tail := run H nodes length fuel next (nextI s i length) (if writes s i length then w+1 else w)
    (NJV_NativeRows.events H log ++ tail.1,tail.2)
   else (NJV_NativeRows.events H log,.stop next)

theorem progresses (s : Scratch) (i length : Nat) (active : i<s.n)
 (continues : returned s i length=true) : i+1≤nextI s i length := by
 have accepted : ¬i<s.n ∨ paired s i ∨ s.cursor+32≤length := of_decide_eq_true continues
 rcases accepted with bad | both | available
 · exact False.elim (bad active)
 · simp only [nextI,if_pos active,if_pos both]; omega
 · by_cases both : paired s i
   · simp only [nextI,if_pos active,if_pos both]; omega
   · simp only [nextI,if_pos active,if_neg both,if_pos available]

theorem native (H : Request → Digest) (nodes : Nat → U8) (length fuel : Nat)
 (s : Scratch) (i w : Nat) (room : s.n≤i+fuel) :
 NJV_NativeRows.Invocation H nodes length fuel s i w
  (run H nodes length fuel s i w).1 (run H nodes length fuel s i w).2 := by
 induction fuel generalizing s i w with
 | zero =>
   have done : s.n≤i := by omega
   simp only [run,if_pos done]
   exact .halt 0 s i w done
 | succ fuel ih =>
   by_cases done : s.n≤i
   · simp only [run,if_pos done]
     exact .halt (fuel+1) s i w done
   · have active : i<s.n := by omega
     cases continues : returned s i length with
     | false =>
       simp only [run,if_neg done,continues,Bool.false_eq_true,if_false]
       exact .stop fuel s (after H nodes length s i w) i w (nextI s i length)
        (if writes s i length then w+1 else w) (capture H nodes length s i w)
        active (continues ▸ cut H nodes length s i w)
     | true =>
       have step := progresses s i length active continues
       have nextRoom : (after H nodes length s i w).n≤nextI s i length+fuel := by
        change s.n≤_; omega
       simp only [run,if_neg done,continues,if_true]
       exact .next fuel s (after H nodes length s i w) i w (nextI s i length)
        (if writes s i length then w+1 else w) (capture H nodes length s i w) _ _
        active (continues ▸ cut H nodes length s i w) (ih _ _ _ nextRoom)
#print axioms progresses
#print axioms native
end AspisR1.NNH_MerkleRowsExecute
