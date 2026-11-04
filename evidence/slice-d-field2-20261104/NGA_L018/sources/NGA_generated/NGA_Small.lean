import NGA_Nine
set_option autoImplicit false
namespace NGA_Small
open Aeneas Aeneas.Std Result NGA_Cell
abbrev Pair := Cache × Cache
abbrev bound : Nat := (2147483647-1)^2

def run : List Pair → Sums → Result Sums
 | [],s => ok s
 | (l,r)::xs,s => do
   let next ← NGA_Nine.run NGA_Nine.trace s l r
   run xs next

def terms (xs : List Pair) (d : Cell) : Nat :=
 (xs.map (fun p => NGA_Nine.product p.1 p.2 d)).sum

theorem product_bound (l r : Cache)
 (hl : NGA_CacheDomain.Bounded l) (hr : NGA_CacheDomain.Bounded r) (d : Cell) :
 NGA_Nine.product l r d ≤ bound := by
 have ha := NGA_Step.bounded_get l hl d
 have hb := NGA_Step.bounded_get r hr d
 calc
  NGA_Nine.product l r d ≤ (2147483647-1)*(2147483647-1) := Nat.mul_le_mul (by omega) (by omega)
  _ = bound := by simp only [bound,pow_two]

/-- Full outer-loop invariant on an arbitrary pre-state; n is exactly the
number of products already accumulated, and n+remaining≤4. -/
theorem loop (xs : List Pair) (s : Sums) (n : Nat)
 (arity : n+xs.length≤4)
 (canonical : ∀ p∈xs, NGA_CacheDomain.Bounded p.1 ∧ NGA_CacheDomain.Bounded p.2)
 (budget : ∀ d, (get s d).val≤n*bound) :
 ∃ out, run xs s=ok out ∧
   (∀ d, (get out d).val=(get s d).val+terms xs d) ∧
   (∀ d, (get out d).val≤(n+xs.length)*bound) := by
 induction xs generalizing s n with
 | nil => exact ⟨s,rfl,by intro d;simp [terms],by simpa using budget⟩
 | cons p ps ih =>
   obtain ⟨hl,hr⟩ := canonical p (by simp)
   have ncap : n≤3 := by simp only [List.length_cons] at arity;omega
   have pre : ∀ d, (get s d).val≤3*(2147483647-1)^2 := by
     intro d;exact (budget d).trans (Nat.mul_le_mul_right bound ncap)
   obtain ⟨next,hnext,vnext⟩ := NGA_Nine.source s p.1 p.2 hl hr pre
   have nextbudget : ∀ d, (get next d).val≤(n+1)*bound := by
     intro d;rw [vnext d,Nat.add_mul,one_mul]
     exact Nat.add_le_add (budget d) (product_bound p.1 p.2 hl hr d)
   obtain ⟨out,hout,vout,bout⟩ := ih next (n+1) (by simpa [Nat.add_assoc] using arity)
     (by intro q hq;exact canonical q (by simp [hq])) nextbudget
   refine ⟨out,?_,?_,?_⟩
   · simp only [run,hnext,bind_tc_ok];exact hout
   · intro d;rw [vout d,vnext d];simp [terms,Nat.add_assoc]
   · simpa [Nat.add_assoc] using bout

abbrev zero : Sums := Array.repeat 3#usize (Array.repeat 3#usize 0#u64)

theorem zero_value (d : Cell) : (get zero d).val=0 := by
 rcases d with ⟨i,j⟩;fin_cases i <;> fin_cases j <;> rfl

theorem source (xs : List Pair) (arity : xs.length≤4)
 (canonical : ∀ p∈xs, NGA_CacheDomain.Bounded p.1 ∧ NGA_CacheDomain.Bounded p.2) :
 ∃ out, run xs zero=ok out ∧ (∀ d, (get out d).val=terms xs d) ∧
   (∀ d, (get out d).val≤xs.length*bound) := by
 obtain ⟨out,ho,hv,hb⟩ := loop xs zero 0 (by simpa using arity) canonical (by intro d;rw [zero_value];simp)
 refine ⟨out,ho,?_,by simpa using hb⟩
 intro d;simpa only [zero_value,Nat.zero_add] using hv d

#print axioms product_bound
#print axioms loop
#print axioms zero_value
#print axioms source
end NGA_Small
