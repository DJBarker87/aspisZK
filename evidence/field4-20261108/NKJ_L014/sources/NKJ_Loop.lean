import NKJ_Accumulate
import NGH_SmallRef
set_option autoImplicit false
namespace NKJ_Loop
open Aeneas Aeneas.Std Result NGA_Cell
abbrev Input := NGA_PreparePairs.Input
abbrev Q := NGA_Cache.Q

def loop : List Input → Sums → Result Sums
 | [],s => ok s
 | x::xs,s => do
   let next ← NKJ_Extracted.field.NKJ_reference.NKJ_accumulate s (NKJ_Cache.words x.1) (NKJ_Cache.words x.2)
   loop xs next

theorem source (xs : List Input) (s : Sums) (n : Nat)
 (arity : n+xs.length≤4)
 (canonical : ∀ x∈xs, NGA_Cache.Canonical x.1 ∧ NGA_Cache.Canonical x.2)
 (budget : ∀ d, (get s d).val≤n*NGA_Small.bound) :
 loop xs s=NGH_SmallRef.loop xs s := by
 induction xs generalizing s n with
 | nil => rfl
 | cons x xs ih =>
   obtain ⟨hl,hr⟩ := canonical x (by simp)
   have ncap : n≤3 := by simp only [List.length_cons] at arity;omega
   have pre : ∀ d, (get s d).val≤3*(2147483647-1)^2 := by
    intro d;exact (budget d).trans (Nat.mul_le_mul_right NGA_Small.bound ncap)
   obtain ⟨l,r,next,hlrun,hrrun,cl,cr,hnext,vnext,_⟩ := NGA_Accumulate.source s x.1 x.2 hl hr pre
   have nextbudget : ∀ d, (get next d).val≤(n+1)*NGA_Small.bound := by
    intro d;rw [vnext d,Nat.add_mul,one_mul]
    exact Nat.add_le_add (budget d) (NGA_Small.product_bound l r cl cr d)
   have tail := ih next (n+1) (by simp only [List.length_cons] at arity;omega)
    (by intro y hy;exact canonical y (by simp [hy])) nextbudget
   simp only [loop,NGH_SmallRef.loop,NGH_AccumulateRef.model_eq,
     NKJ_Accumulate.source s x.1 x.2 hl hr pre,hnext,bind_tc_ok]
   exact tail

def run (xs : List Input) : Result NKJ_Extracted.field.QM31 := do
 let s ← loop xs NGA_Small.zero
 NKJ_Extracted.field.qm31_from_karatsuba_channel_sums s

theorem value (xs : List Input) (arity : xs.length≤4)
 (canonical : ∀ x∈xs, NGA_Cache.Canonical x.1 ∧ NGA_Cache.Canonical x.2) :
 run xs=(do let q ← NGA_SmallResult.sourceModel xs; ok (NKJ_Extracted.fromCanonical q)) := by
 have h := source xs NGA_Small.zero 0 (by simpa using arity) canonical (by
  intro d;rw [NGA_Small.zero_value];simp)
 simp only [run,h,NGH_SmallRef.loop_eq,NGA_SmallResult.sourceModel,
  NKJ_Extracted.field.qm31_from_karatsuba_channel_sums,bind_assoc_eq]
#print axioms source
#print axioms value
end NKJ_Loop
