import NKR_DigestInvocation
/-! Reviewed(ai)(5) source transcription, NKR_Digest_prefix_split.rs.txt
SHA256 2205e30d801d33119871f5d82850426487a75ae3a565d5ea9576601dfb8d34a9. Assertions quote: `l.calls=3`, exact
child kind/high/opened/present/digest, `l.kinds[lane]=1`, both add operands,
and all `out[group][lane]` raw limbs = adds for group1 or original prestate
for the two framed groups. Original K018inputfailure/K034TIMEOUT retained. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_DigestPrefixStep
open Aeneas Aeneas.Std Result
open NKI_InitialPrefix (Public Openings Selectors)
open NKR_DigestChildren (Children Pair)
open NKR_DigestCuts (Sums PrefixFrames Event zero child before)

/-- NKR_Digest_prefix_step_cut: one actual source binding block at arbitrary
full3x2prestate, not a rerun of the retired12event prefix. Every child input,
two addition operands and the full return/frame are asserted. -/
def Cut (p : Public) (o : Openings) (s : Selectors) (c : Children) (g : Fin 4)
 (pre : Sums) (added : Pair) (out : Sums) (events : Fin 3 → Event) (calls : Nat) : Prop :=
 calls=3 ∧ (events 0).kind=(if g.val=2 then 12 else 11) ∧
 (events 0).high=NKR_DigestCuts.high s g ∧ (events 0).opened=o.z ∧
 (events 0).present=(NKR_DigestCuts.digests p g).isSome ∧
 (events 0).digest=NKR_DigestCuts.digest (NKR_DigestCuts.digests p g) ∧
 (∀ j : Fin 2,(events ⟨1+j.val,by have h:=j.isLt;omega⟩).kind=1 ∧
  (events ⟨1+j.val,by have h:=j.isLt;omega⟩).left=pre 1 j ∧
  (events ⟨1+j.val,by have h:=j.isLt;omega⟩).right=child c g j) ∧
 out=(![pre 0,added,pre 2] : Sums)

def events (p : Public) (o : Openings) (s : Selectors) (c : Children) (g : Fin 4) (pre : Sums) : Fin 3 → Event :=
 ![NKR_DigestCuts.childEvent p o s g,NKR_DigestCuts.addEvent p o s (pre 1 0) (child c g 0),
 NKR_DigestCuts.addEvent p o s (pre 1 1) (child c g 1)]

theorem cut (p : Public) (o : Openings) (s : Selectors) (c : Children) (g : Fin 4) (pre : Sums) (added : Pair) :
 Cut p o s c g pre added ![pre 0,added,pre 2] (events p o s c g pre) 3 := by
 refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_,rfl⟩
 intro j;fin_cases j <;> exact ⟨rfl,rfl,rfl⟩

inductive Trace (p : Public) (o : Openings) (s : Selectors) (c : Children) : List (Fin 4) → Sums → Sums → Prop
 | nil (pre) : Trace p o s c [] pre pre
 | cons {g gs pre added out} :
  NKR_DigestAdd.add (pre 1) (child c g)=ok added →
  Cut p o s c g pre added ![pre 0,added,pre 2] (events p o s c g pre) 3 →
  Trace p o s c gs ![pre 0,added,pre 2] out → Trace p o s c (g::gs) pre out

/-- Finite4block induction associates each NEW native arbitrary-prestate
step with the SAME source reply from PrefixArithmetic. Full framed groups
remain zero from the actual initialization, never an input restriction. -/
theorem four (p : Public) (o : Openings) (s : Selectors) (c : Children) (v : PrefixFrames)
 (h : NKR_DigestInvocation.PrefixArithmetic c v) :
 Trace p o s c (List.finRange 4) ![zero,zero,zero] ![zero,v 3,zero] := by
 change Trace p o s c [0,1,2,3] ![zero,zero,zero] ![zero,v 3,zero]
 apply Trace.cons (added:=v 0) (h 0) (cut p o s c 0 _ _)
 apply Trace.cons (added:=v 1) (h 1) (cut p o s c 1 _ _)
 apply Trace.cons (added:=v 2) (h 2) (cut p o s c 2 _ _)
 apply Trace.cons (added:=v 3) (h 3) (cut p o s c 3 _ _)
 exact .nil _
#print axioms cut
#print axioms four
end AspisR1.NKR_DigestPrefixStep
end
