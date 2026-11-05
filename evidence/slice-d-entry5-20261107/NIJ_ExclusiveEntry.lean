import NIJ_SdkWriteFrame
import NHY_SnapshotRoot
set_option autoImplicit false
namespace NIJ_ExclusiveEntry
open AspisR1.S2Trust AspisR1.S2W_D189Entry

theorem valid {F : Type} (s : Heap F) (a token owner : Nat)
 (before : Valid s) (empty : s.guards=[]) (zero : ∀ c, s.counter c=0)
 (external : ∀ c, s.external c=0) (enabled : Enabled s (.exclusive a token owner)) :
 Valid (acquire s (s.accounts a).1 token owner .exclusive) := by
 rcases before with ⟨pairs,bounds,live,owners⟩
 refine ⟨by simp [acquire,empty],?_,?_,owners⟩
 · intro cell
   by_cases same : cell=(s.accounts a).1
   · subst cell
     simp [acquire,put,count,empty,zero,external,minCounter,maxCounter]
   · simpa [acquire,put,count,empty,zero,external,same,Ne.symm same]
       using bounds cell
 · intro g member
   simp only [acquire,empty,List.mem_cons,List.not_mem_nil,or_false] at member
   subst g
   exact ⟨(owners a enabled.1).2,rfl⟩

theorem entry_valid (e : Entry) (a token owner : Nat) (before : Valid e.heap)
 (enabled : Enabled e.heap (.exclusive a token owner)) :
 Valid (acquire e.heap (e.heap.accounts a).1 token owner .exclusive) :=
 valid e.heap a token owner before rfl (fun _ => rfl) (fun _ => rfl) enabled

theorem counter {F : Type} (s : Heap F) (a token owner : Nat) :
 (acquire s (s.accounts a).1 token owner .exclusive).counter (s.accounts a).1 = -1 := by
 simp [acquire,put]

theorem found {F : Type} (s : Heap F) (a token owner : Nat) :
 lookup (acquire s (s.accounts a).1 token owner .exclusive) token =
 some ⟨token,(s.accounts a).1,owner,.exclusive,(s.payload (s.accounts a).1).descriptor⟩ := by
 simp [lookup,acquire]

#print axioms valid
#print axioms entry_valid
#print axioms counter
#print axioms found
end NIJ_ExclusiveEntry
