import CuSavingsRhoReference

/-! Vector frame and fresh-coordinate invariant. Each query updates every
coefficient once while terms is unchanged, then increments terms once.
The source caller still has to supply its actual index sequence and basis.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoVector
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoValue CuSavingsRhoPush CuSavingsRhoPushStep CuSavingsRhoState
open CuSavingsRhoInitRow CuSavingsRhoReference CuSavingsResidues
open CuSavingsRhoFinishModel

theorem canonical_replace (self : verifier.BatchedWeights) (index : Usize) (row : Raw4) :
    canonicalSlice (replaceRow self index row) =
      Slice.set (canonicalSlice self) index (canonicalValue row) := by
  apply Subtype.ext
  simp only [canonicalSlice,replaceRow,Slice.set,Slice.setAtNat,List.map_set]

def referenceAt (weights : Slice field.QM31) (index : Usize)
    (power : field.QM31) (basis : U32) : Result (Slice field.QM31) := do
  let weight ← alloc.vec.Vec.index
    (Aeneas.Std.core.slice.index.SliceIndexUsizeSlice field.QM31) weights index
  let out ← referenceStep weight power basis
  .ok (Slice.set weights index out)

theorem source_vector_step (self : verifier.BatchedWeights) (index : Usize)
    (power : field.QM31) (basis : U32) (hi : index.val < self.raw.val.length)
    (hr : ∀ j : Fin 4,RhoBound (wordAt (self.raw.val[index.val]'hi) j).val self.terms.val)
    (hp : Canonical power) (hb : basis.val < AspisV8R17.RawReducer.P) :
    ∃ row : Raw4,
      verifier.BatchedWeights.push self index power basis = .ok (replaceRow self index row) ∧
      referenceAt (canonicalSlice self) index power basis =
        .ok (canonicalSlice (replaceRow self index row)) ∧
      ∀ j : Fin 4,RhoBound (wordAt row j).val (self.terms.val+1) := by
  obtain ⟨row,hrun,href,hbound⟩ := push_reference self index power basis hi hr hp hb
  refine ⟨row,hrun,?_,hbound⟩
  have hc : index.val < (canonicalSlice self).val.length := by
    simpa only [canonicalSlice,List.length_map] using hi
  unfold referenceAt
  rw [vec_read (canonicalSlice self) index hc]
  simp only [bind_tc_ok]
  change (do
    let out ← referenceStep (canonicalValue (self.raw.val[index.val]'hi)) power basis
    .ok (Slice.set (canonicalSlice self) index out)) = _
  rw [href]
  simp only [bind_tc_ok]
  exact congrArg Result.ok (canonical_replace self index row).symm

def Good (self : verifier.BatchedWeights) (done : List Nat) : Prop :=
  ∀ (i : Usize) (hi : i.val < self.raw.val.length) (j : Fin 4),
    RhoBound (wordAt (self.raw.val[i.val]'hi) j).val
      (self.terms.val + if i.val ∈ done then 1 else 0)

theorem good_replace (self : verifier.BatchedWeights) (done : List Nat)
    (index : Usize) (row : Raw4) (hi : index.val < self.raw.val.length)
    (hgood : Good self done)
    (hrow : ∀ j : Fin 4,RhoBound (wordAt row j).val (self.terms.val+1)) :
    Good (replaceRow self index row) (index.val::done) := by
  intro i hi' j
  have hi0 : i.val < self.raw.val.length := by
    simpa only [replace_length] using hi'
  by_cases heq : i.val = index.val
  · have hei : i = index := UScalar.eq_of_val_eq heq
    subst i
    simpa only [replace_read self index row hi,replace_terms,List.mem_cons,
      true_or,ite_true] using hrow j
  · have hold := hgood i hi0 j
    change RhoBound (wordAt ((self.raw.val.set index.val row)[i.val]'_) j).val
      (self.terms.val + if i.val ∈ index.val::done then 1 else 0)
    simp only [List.getElem_set,if_neg (Ne.symm heq),List.mem_cons,heq,false_or]
    exact hold

def updates (power : field.QM31) : List (Usize × U32) → verifier.BatchedWeights →
    Result verifier.BatchedWeights
  | [],self => .ok self
  | (index,basis)::tail,self => do
    let next ← verifier.BatchedWeights.push self index power basis
    updates power tail next

def referenceUpdates (power : field.QM31) : List (Usize × U32) → Slice field.QM31 →
    Result (Slice field.QM31)
  | [],weights => .ok weights
  | (index,basis)::tail,weights => do
    let next ← referenceAt weights index power basis
    referenceUpdates power tail next

theorem updates_success (items : List (Usize × U32)) (self : verifier.BatchedWeights)
    (done : List Nat) (power : field.QM31) (hgood : Good self done)
    (hp : Canonical power)
    (hi : ∀ pair ∈ items,pair.1.val < self.raw.val.length)
    (hb : ∀ pair ∈ items,pair.2.val < AspisV8R17.RawReducer.P)
    (hfresh : ∀ pair ∈ items,pair.1.val ∉ done)
    (hnodup : (items.map (fun pair => pair.1.val)).Nodup) :
    ∃ out : verifier.BatchedWeights,
      updates power items self = .ok out ∧
      referenceUpdates power items (canonicalSlice self) = .ok (canonicalSlice out) ∧
      out.terms = self.terms ∧ out.raw.val.length = self.raw.val.length ∧
      Good out ((items.map (fun pair => pair.1.val)).reverse ++ done) := by
  induction items generalizing self done with
  | nil => exact ⟨self,rfl,rfl,rfl,rfl,by simpa using hgood⟩
  | cons pair tail ih =>
    rcases pair with ⟨index,basis⟩
    have hmem : (index,basis) ∈ (index,basis)::tail := by simp only [List.mem_cons,true_or]
    have hidx := hi _ hmem
    have hnot := hfresh _ hmem
    have hbound : ∀ j : Fin 4,
        RhoBound (wordAt (self.raw.val[index.val]'hidx) j).val self.terms.val := by
      intro j
      simpa only [if_neg hnot,Nat.add_zero] using hgood index hidx j
    obtain ⟨row,hrun,href,hrb⟩ := source_vector_step self index power basis hidx hbound hp (hb _ hmem)
    have hg := good_replace self done index row hidx hgood hrb
    have hn := List.nodup_cons.mp hnodup
    obtain ⟨out,hout,houtref,hterms,hlen,hgout⟩ := ih (replaceRow self index row)
      (index.val::done) hg
      (fun p h => by simpa only [replace_length] using hi p (List.mem_cons_of_mem _ h))
      (fun p h => hb p (List.mem_cons_of_mem _ h))
      (fun p h => by
        have hne : p.1.val ≠ index.val := by
          intro heq
          exact hn.1 (List.mem_map.mpr ⟨p,h,heq⟩)
        simpa only [List.mem_cons,not_or] using
          And.intro hne (hfresh p (List.mem_cons_of_mem _ h))) hn.2
    refine ⟨out,?_,?_,hterms.trans rfl,hlen.trans (replace_length _ _ _),?_⟩
    · simp only [updates,hrun,bind_tc_ok,hout]
    · simp only [referenceUpdates,href,bind_tc_ok,houtref]
    · simpa only [List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hgout

#print axioms source_vector_step
#print axioms good_replace
#print axioms updates_success
end AspisR1.CuSavingsRhoVector
