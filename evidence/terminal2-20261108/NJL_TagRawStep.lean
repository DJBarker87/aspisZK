import NJL_TagWords
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_TagRawStep
open Aeneas Aeneas.Std Result
open NJB_TagRaw (B)
abbrev State := Fin 4 → U64
structure Event where
 left : U64
 right : U64
/-- NJB_K068/K069 exact4-call/next/raw-post transcription on the model's
U64 carriers. Natural sums are exact because raw≤3B and replies≤B. -/
def Cut (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (term : Fin 272)
 (before after products : State) (events : Fin 4 → Event) (calls next : Nat) : Prop :=
 calls=4 ∧ next=term.val+1 ∧
 (∀ i,(events i).left=NJL_TagWords.highWord s term i ∧ (events i).right=NJL_TagWords.tagWord term) ∧
 (∀ i,(after i).val=(before i).val+(products i).val)
def reference (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (term : Fin 272) (before : State) : Result State := do
 let p0 ← UScalar.mul (NJL_TagWords.highWord s term 0) (NJL_TagWords.tagWord term)
 let r0 ← UScalar.add (before 0) p0
 let p1 ← UScalar.mul (NJL_TagWords.highWord s term 1) (NJL_TagWords.tagWord term)
 let r1 ← UScalar.add (before 1) p1
 let p2 ← UScalar.mul (NJL_TagWords.highWord s term 2) (NJL_TagWords.tagWord term)
 let r2 ← UScalar.add (before 2) p2
 let p3 ← UScalar.mul (NJL_TagWords.highWord s term 3) (NJL_TagWords.tagWord term)
 let r3 ← UScalar.add (before 3) p3
 ok ![r0,r1,r2,r3]
theorem add (raw product : U64) (k : Nat) (hk : k<4) (hr : raw.val≤k*B) (hp : product.val≤B) :
 ∃ out,UScalar.add raw product=ok out ∧ out.val=raw.val+product.val ∧ out.val≤(k+1)*B := by
 have bound := NJB_TagRaw.step_bound raw.val product.val k hk hr hp
 obtain ⟨out,call,value⟩ := WP.spec_imp_exists (U64.add_spec (x:=raw) (y:=product) (by scalar_tac))
 exact ⟨out,call,value,by rw [value];exact bound.1⟩
/-- Every product reply is the actual checked integer product, with its exact
natural-value law. Four adds follow each product in SOURCE limb order. -/
theorem source (s : FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors) (term : Fin 272) (before : State)
 (k : Nat) (hk : k<4) (hs : FIw_ArrayValue.canonical s.high) (hr : ∀ i,(before i).val≤k*B) :
 ∃ products after events,
 reference s term before=ok after ∧ Cut s term before after products events 4 (term.val+1) ∧
 (∀ i,UScalar.mul (NJL_TagWords.highWord s term i) (NJL_TagWords.tagWord term)=ok (products i) ∧
   (products i).val=(NJL_TagWords.highWord s term i).val*(NJL_TagWords.tagWord term).val ∧ (products i).val≤B) ∧
 (∀ i,UScalar.add (before i) (products i)=ok (after i)) ∧
 (∀ i,(after i).val≤(k+1)*B) := by
 obtain ⟨p0,m0,v0,b0⟩ := NJL_TagWords.product s term 0 hs
 obtain ⟨r0,a0,w0,c0⟩ := add (before 0) p0 k hk (hr 0) b0
 obtain ⟨p1,m1,v1,b1⟩ := NJL_TagWords.product s term 1 hs
 obtain ⟨r1,a1,w1,c1⟩ := add (before 1) p1 k hk (hr 1) b1
 obtain ⟨p2,m2,v2,b2⟩ := NJL_TagWords.product s term 2 hs
 obtain ⟨r2,a2,w2,c2⟩ := add (before 2) p2 k hk (hr 2) b2
 obtain ⟨p3,m3,v3,b3⟩ := NJL_TagWords.product s term 3 hs
 obtain ⟨r3,a3,w3,c3⟩ := add (before 3) p3 k hk (hr 3) b3
 let products : State := ![p0,p1,p2,p3]
 let after : State := ![r0,r1,r2,r3]
 let events : Fin 4 → Event := fun i=>⟨NJL_TagWords.highWord s term i,NJL_TagWords.tagWord term⟩
 refine ⟨products,after,events,?_,?_,?_,?_,?_⟩
 · simp only [reference,m0,a0,m1,a1,m2,a2,m3,a3,bind_tc_ok];rfl
 · refine ⟨rfl,rfl,fun _=>⟨rfl,rfl⟩,?_⟩
   intro i;fin_cases i
   · exact w0
   · exact w1
   · exact w2
   · exact w3
 · intro i;fin_cases i
   · exact ⟨m0,v0,b0⟩
   · exact ⟨m1,v1,b1⟩
   · exact ⟨m2,v2,b2⟩
   · exact ⟨m3,v3,b3⟩
 · intro i;fin_cases i
   · exact a0
   · exact a1
   · exact a2
   · exact a3
 · intro i;fin_cases i
   · exact c0
   · exact c1
   · exact c2
   · exact c3
#print axioms add
#print axioms source
end AspisR1.NJL_TagRawStep
end
