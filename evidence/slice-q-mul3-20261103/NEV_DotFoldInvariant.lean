import NEV_DotScalar
import NEG_Induction
set_option autoImplicit false
noncomputable section
namespace NEV_DotFoldInvariant
open Aeneas Aeneas.Std Result
/-- Literal checked-add recurrence for one scalar lane, not field arithmetic. -/
def run (initial : U64) : List U64 → Result U64
 | [] => ok initial
 | head::tail => do let next ← initial+head;run next tail
/-- Arbitrary pre-state and arbitrary bounded product replies. Every checked
addition is total; the SAME returned word has the retained natural prefix bound. -/
theorem total (products : List U64) (initial : U64) (n : Nat)
    (width : n+products.length≤4) (before : initial.val≤n*NEG_DotDomain.B)
    (bounded : ∀ product∈products,product.val≤NEG_DotDomain.B) :
    ∃ out,run initial products=ok out ∧
      out.val=initial.val+(products.map (fun x=>x.val)).sum ∧
      out.val≤(n+products.length)*NEG_DotDomain.B := by
  induction products generalizing initial n with
  | nil => exact ⟨initial,rfl,by simp,before⟩
  | cons head tail ih =>
    have headBound:=bounded head (by simp)
    have small : n<4 := by simp only [List.length_cons] at width;omega
    have safe:=NEG_DotDomain.term_safe n initial.val head.val small before headBound
    obtain ⟨next,add,value⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x:=initial) (y:=head)
        (by norm_num [UScalar.max,UScalar.size,U64.max,U64.size,U64.numBits];norm_num at safe;omega))
    have nextBound : next.val≤(n+1)*NEG_DotDomain.B := by
      rw [value];exact NEG_DotDomain.term_invariant n initial.val head.val before headBound
    obtain ⟨out,rest,meaning,bound⟩ := ih next (n+1)
      (by simp only [List.length_cons] at width;omega) nextBound
      (by intro p hp;exact bounded p (by simp [hp]))
    refine ⟨out,by simp only [run,add,bind_tc_ok,rest],?_,?_⟩
    · simp only [List.map_cons,List.sum_cons]
      rw [meaning,value];omega
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using bound
/-- The actual success witness identifies the SAME prefix word; it is not a
successful whole-caller premise. This is exactly the native one-cell bound. -/
theorem native_domain (products : List U64) (width : products.length≤3)
    (bounded : ∀ product∈products,product.val≤NEG_DotDomain.B)
    (before : U64) (reached : run 0#u64 products=ok before) :
    before.val≤13835058029512359948 := by
  obtain ⟨out,actual,meaning,bound⟩ := total products 0#u64 0 (by omega) (by simp) bounded
  have same : out=before := Result.ok.inj (actual.symm.trans reached)
  subst out
  have cap:=Nat.mul_le_mul_right NEG_DotDomain.B width
  norm_num [NEG_DotDomain.B] at bound cap
  omega
#print axioms total
#print axioms native_domain
end NEV_DotFoldInvariant
end
