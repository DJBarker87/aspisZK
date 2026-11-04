import NGA_Small
import NFT_Karatsuba
set_option autoImplicit false
namespace NGA_PreparePairs
open Aeneas Aeneas.Std Result
abbrev Q := NGA_Cache.Q
abbrev Input := Q × Q
abbrev Pair := NGA_Small.Pair
abbrev Canonical := NGA_Cache.Canonical

def PairFor (x : Input) (p : Pair) : Prop :=
 NGA_Cache.prelude x.1=ok p.1 ∧ NGA_Cache.prelude x.2=ok p.2 ∧
 NGA_CacheDomain.Bounded p.1 ∧ NGA_CacheDomain.Bounded p.2

def prepare : List Input → Result (List Pair)
 | [] => ok []
 | x::xs => do
   let l ← NGA_Cache.prelude x.1
   let r ← NGA_Cache.prelude x.2
   let tail ← prepare xs
   ok ((l,r)::tail)

theorem source (xs : List Input)
 (canonical : ∀ x∈xs, Canonical x.1 ∧ Canonical x.2) :
 ∃ cs, prepare xs=ok cs ∧ List.Forall₂ PairFor xs cs ∧
   cs.length=xs.length ∧
   ∀ p∈cs, NGA_CacheDomain.Bounded p.1 ∧ NGA_CacheDomain.Bounded p.2 := by
 induction xs with
 | nil => exact ⟨[],rfl,.nil,rfl,by simp⟩
 | cons x xs ih =>
   obtain ⟨hl,hr⟩ := canonical x (by simp)
   obtain ⟨l,hleft,cl,_⟩ := NGA_CacheDomain.source x.1 hl
   obtain ⟨r,hright,cr,_⟩ := NGA_CacheDomain.source x.2 hr
   obtain ⟨cs,hcs,assoc,length,domain⟩ := ih (by intro q hq;exact canonical q (by simp [hq]))
   refine ⟨(l,r)::cs,?_,List.Forall₂.cons ⟨hleft,hright,cl,cr⟩ assoc,by simp only [List.length_cons,length],?_⟩
   · simp only [prepare,hleft,hright,hcs,bind_tc_ok]
   · intro p hp
     rcases List.mem_cons.mp hp with hp | hp
     · subst p;exact ⟨cl,cr⟩
     · exact domain p hp

/-- Source chronology: prepare only the current pair, update the same sums,
then advance. No whole-buffer/native loop is used. -/
def run : List Input → NGA_Cell.Sums → Result NGA_Cell.Sums
 | [],s => ok s
 | x::xs,s => do
   let l ← NGA_Cache.prelude x.1
   let r ← NGA_Cache.prelude x.2
   let next ← NGA_Nine.run NGA_Nine.trace s l r
   run xs next

theorem same_run (xs : List Input) (cs : List Pair) (h : List.Forall₂ PairFor xs cs)
 (s : NGA_Cell.Sums) : run xs s=NGA_Small.run cs s := by
 induction h generalizing s with
 | nil => rfl
 | @cons x p xs ps hp h ih =>
   simp only [run,NGA_Small.run,hp.1,hp.2.1,bind_tc_ok]
   cases hr : NGA_Nine.run NGA_Nine.trace s p.1 p.2 with
   | ok next => simp only [bind_tc_ok];exact ih next
   | fail e => rfl
   | div => rfl

#print axioms source
#print axioms same_run
end NGA_PreparePairs
