import NIS_ErrorJoin
set_option autoImplicit false
namespace NIJ_StringCleanup

def release {A : Type} (heap : Nat → Option A) (base capacity : Nat) (k : Nat) : Option A :=
 if base≤k ∧ k<base+capacity then none else heap k

theorem outside {A : Type} (heap : Nat → Option A) (base capacity k : Nat)
 (separate : k<base ∨ base+capacity≤k) : release heap base capacity k=heap k := by
 have h : ¬(base≤k ∧ k<base+capacity) := by omega
 simp only [release,h,ite_false]

theorem inside {A : Type} (heap : Nat → Option A) (base capacity k : Nat)
 (lo : base≤k) (hi : k<base+capacity) : release heap base capacity k=none := by
 simp only [release,and_self,lo,hi,ite_true]

/-- Fresh-allocation separation is the existing allocator primitive domain;
this proves the complete account observation frame for deallocation. -/
theorem account_frame {A I : Type} (heap : Nat → Option A) (addresses : I → List Nat)
 (base capacity : Nat)
 (fresh : ∀ i k, k∈addresses i → k<base ∨ base+capacity≤k) (i : I) :
 (addresses i).map (release heap base capacity)=(addresses i).map heap := by
 apply List.map_congr_left
 intro k member
 exact outside heap base capacity k (fresh i k member)

/-- Growth may free the original allocation and cleanup the replacement.
Both use the same separation domain; no account byte can change. -/
theorem growth_frame {A I : Type} (heap : Nat → Option A) (addresses : I → List Nat)
 (old fresh oldCapacity freshCapacity : Nat)
 (oldSeparate : ∀ i k, k∈addresses i → k<old ∨ old+oldCapacity≤k)
 (newSeparate : ∀ i k, k∈addresses i → k<fresh ∨ fresh+freshCapacity≤k) (i : I) :
 (addresses i).map (release (release heap old oldCapacity) fresh freshCapacity)=
 (addresses i).map heap := by
 rw [account_frame _ addresses fresh freshCapacity newSeparate i]
 exact account_frame heap addresses old oldCapacity oldSeparate i

#print axioms outside
#print axioms inside
#print axioms account_frame
#print axioms growth_frame
end NIJ_StringCleanup
