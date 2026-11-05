import NHS_ContextQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHW_LoopCongruence
open Aeneas Aeneas.Std Result AspisR1Stage2 NFG_QueryLoopDefs
/-- Abstract finite induction keeps concrete dictionaries out of reduction. -/
theorem source (first second : Query) (p : verifier.Prepared) (start : Nat)
 (finish : Usize)
 (same : ∀ a b, NFS_QueryInvariant.Domain p start finish.val a b → a.next.val<finish.val →
   first a b=second a b)
 (preserve : ∀ a b after pending, NFS_QueryInvariant.Domain p start finish.val a b →
   a.next.val<finish.val → second a b=ok (.Ok (after,pending)) →
   NFS_QueryInvariant.Domain p start finish.val after pending)
 (fuel : Nat) (state : State) (valid : NFS_QueryLoopRoot.Valid p start finish.val state) :
 run first finish fuel state=run second finish fuel state := by
 induction fuel generalizing state with
 | zero => cases state with | Err e=>rfl | Ok pair=>cases pair;rfl
 | succ fuel ih =>
   cases state with
   | Err error => rfl
   | Ok pair =>
     rcases pair with ⟨a,b⟩
     by_cases stopped : a.next≥finish
     · simp only [run,stopped,if_true]
     · have inside : a.next.val<finish.val := Nat.lt_of_not_ge stopped
       simp only [run,stopped,if_false,same a b valid inside]
       cases h : second a b with
       | fail e => rfl
       | div => rfl
       | ok next =>
         simp only [bind_tc_ok]
         apply ih
         cases next with
         | Err error => trivial
         | Ok pair =>
           rcases pair with ⟨after,pending⟩
           exact preserve a b after pending valid inside h
#print axioms source
end AspisR1.NHW_LoopCongruence
