import XRy_ClaimFold
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers
set_option autoImplicit false
namespace XRy_ListPowers

theorem total (n : Nat) (x p : C.E)
 (hx : XRy_WideMultiply.Canonical x) (hp : XRy_WideMultiply.Canonical p) :
 ∃ xs, XRn_Join_powers x n p = ok xs ∧ xs.length=n ∧ XRy_ClaimFold.canonicalList xs := by
 induction n generalizing p with
 | zero => exact ⟨[],rfl,rfl,by intro a h; cases h⟩
 | succ n ih =>
   cases n with
   | zero => exact ⟨[p],rfl,rfl,by intro a h; simp only [List.mem_singleton] at h; exact h ▸ hp⟩
   | succ m =>
     obtain ⟨next,en,hn,_⟩ := XRy_ClaimArithmetic.multiply p x hp hx
     obtain ⟨xs,ex,hl,hc⟩ := ih next hn
     refine ⟨p::xs,?_,by simp only [List.length_cons,hl],?_⟩
     · simp only [XRn_Join_powers,en,ex,bind_tc_ok]
     · intro a h
       rcases List.mem_cons.mp h with h | h
       · exact h ▸ hp
       · exact hc a h

#print axioms total
end XRy_ListPowers
