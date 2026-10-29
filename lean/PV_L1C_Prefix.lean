import PV_RJ4IDB_OpenInputs
/-! Compositional trace equations only. No native producer is installed.
All indices may denote rejected, failed or divergent execution prefixes. -/
set_option autoImplicit false
namespace PV_L1C
open PV_RJ4IDB
variable {I A : Type}

def splice (l r : NativeTrace A) : NativeTrace A :=
 ⟨l.events ++ r.events,r.terminal⟩

theorem counts_append (l r : List NativeEvent) :
 nativeCounts (l++r) = nativeCounts l ++ nativeCounts r := List.filterMap_append

theorem rejections_append (l r : List NativeEvent) :
 nativeRejections (l++r) = nativeRejections l ++ nativeRejections r := List.filterMap_append

theorem times_append (l r : List NativeEvent) :
 nativeTimes (l++r) = nativeTimes l ++ nativeTimes r := List.filterMap_append

theorem oracle_append (l r : List NativeEvent) :
 nativeOracle (l++r) = nativeOracle l ++ nativeOracle r := List.filterMap_append

theorem side_append (l r : List NativeEvent) :
 nativeSide (l++r) = nativeSide l ++ nativeSide r := List.filterMap_append

/-- Exact requested type, conditional on the two stage producers. This is not
an instance for the client, and no hypothesis is discharged by this lemma. -/
theorem count_splice (actualL actualR : I → List Nat × List Nat)
 (l r : I → NativeTrace A)
 (hl : OpenInputs.L1_COUNT_TRACE actualL l)
 (hr : OpenInputs.L1_COUNT_TRACE actualR r) :
 OpenInputs.L1_COUNT_TRACE
  (fun i => ((actualL i).1 ++ (actualR i).1,(actualL i).2 ++ (actualR i).2))
  (fun i => splice (l i) (r i)) := by
 intro i
 dsimp only [splice]
 rw [hl i,hr i]
 exact Prod.ext (counts_append _ _).symm (rejections_append _ _).symm

theorem time_splice (actualL actualR : I → List Bytes) (l r : I → NativeTrace A)
 (hl : OpenInputs.L1_TIME_TRACE actualL l)
 (hr : OpenInputs.L1_TIME_TRACE actualR r) :
 OpenInputs.L1_TIME_TRACE (fun i => actualL i ++ actualR i)
  (fun i => splice (l i) (r i)) := by
 intro i
 dsimp only [splice]
 rw [hl i,hr i]
 exact (times_append _ _).symm

theorem oracle_splice (actualL actualR : I → List (Bytes × Bytes))
 (l r : I → NativeTrace A)
 (hl : OpenInputs.L1_ORACLE_PREFIX actualL l)
 (hr : OpenInputs.L1_ORACLE_PREFIX actualR r) :
 OpenInputs.L1_ORACLE_PREFIX (fun i => actualL i ++ actualR i)
  (fun i => splice (l i) (r i)) := by
 intro i
 dsimp only [splice]
 rw [hl i,hr i]
 exact (oracle_append _ _).symm

theorem side_splice (actualL actualR : I → List (Bytes × Bytes))
 (l r : I → NativeTrace A)
 (hl : OpenInputs.L1_RETAINED_SIDECHANNELS actualL l)
 (hr : OpenInputs.L1_RETAINED_SIDECHANNELS actualR r) :
 OpenInputs.L1_RETAINED_SIDECHANNELS (fun i => actualL i ++ actualR i)
  (fun i => splice (l i) (r i)) := by
 intro i
 dsimp only [splice]
 rw [hl i,hr i]
 exact (side_append _ _).symm

#print axioms counts_append
#print axioms rejections_append
#print axioms times_append
#print axioms oracle_append
#print axioms side_append
#print axioms count_splice
#print axioms time_splice
#print axioms oracle_splice
#print axioms side_splice
end PV_L1C
