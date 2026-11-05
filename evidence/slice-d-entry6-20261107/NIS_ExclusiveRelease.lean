import NIS_ExclusiveEntry
import NIS_SdkWriteLoop
set_option autoImplicit false
namespace NIJ_ExclusiveRelease
open AspisR1.S2Trust

def guard {F : Type} (s : Heap F) (a token owner : Nat) : Guard :=
 ⟨token,(s.accounts a).1,owner,.exclusive,(s.payload (s.accounts a).1).descriptor⟩

theorem acquired {F : Type} (s : Heap F) (a token owner : Nat)
 (fresh : lookup s token=none) (zero : s.counter (s.accounts a).1=0) :
 release (acquire s (s.accounts a).1 token owner .exclusive) (guard s a token owner)=s := by
 have keep:=NHJ_SdkBracket.filter_fresh s.guards token fresh
 have counters : put (put s.counter (s.accounts a).1 (-1)) (s.accounts a).1 0=s.counter := by
  funext c
  by_cases same : c=(s.accounts a).1 <;> simp [put,same,zero]
 simpa [release,acquire,guard,keep,counters]

theorem write_commutes {F : Type} (s : Heap F) (g : Guard) (i : Nat) (v : UInt8) :
 release (writeAt s g i v) g=writeAt (release s g) g i v := rfl

/-- The real exclusive token is consumed once after the entire SAME write.
This restores the counter but keeps every copied byte. -/
theorem copied {F : Type} (s : Heap F) (a token owner : Nat)
 (source : Nat → UInt8) (start n : Nat)
 (fresh : lookup s token=none) (zero : s.counter (s.accounts a).1=0) :
 release (NIJ_SdkWriteLoop.copy (acquire s (s.accounts a).1 token owner .exclusive)
   (guard s a token owner) source start n) (guard s a token owner)=
 NIJ_SdkWriteLoop.copy s (guard s a token owner) source start n := by
 induction n with
 | zero => exact acquired s a token owner fresh zero
 | succ n ih => rw [NIJ_SdkWriteLoop.copy,write_commutes,ih];rfl

#print axioms acquired
#print axioms write_commutes
#print axioms copied
end NIJ_ExclusiveRelease
