import CuSavingsRhoQueryBatch

/-! Complete finite arithmetic pipeline with failures/divergence between queries.
This consumes actual push, old scalar/add arithmetic and actual source finish.
It does not assert that new/zip or the enclosing verifier emits this index list.
-/
set_option autoImplicit false
namespace AspisR1.CuSavingsRhoBatches
open Aeneas Aeneas.Std Result AspisR1CuRho
open CuSavingsRhoValue CuSavingsRhoPush CuSavingsRhoPushStep CuSavingsRhoState
open CuSavingsRhoInitRow CuSavingsRhoReference CuSavingsRhoVector CuSavingsResidues
open CuSavingsRhoFinishModel CuSavingsRhoQueryBatch

structure Input where
  power : field.QM31
  items : List (Usize × U32)

def Admitted (input : Input) (length : Nat) : Prop :=
  Canonical input.power ∧
  (∀ pair ∈ input.items,pair.1.val < length) ∧
  (∀ pair ∈ input.items,pair.2.val < AspisV8R17.RawReducer.P) ∧
  (input.items.map (fun pair => pair.1.val)).Nodup ∧
  (∀ i : Usize,i.val < length → i.val ∈ input.items.map (fun pair => pair.1.val))

def optimized : List (Result Input) → verifier.BatchedWeights → Slice field.QM31 →
    Result (Slice field.QM31)
  | [],self,template => AspisR1CuRhoSource.verifier.BatchedWeights.finish self template
  | input::tail,self,template => do
    let data ← input
    let next ← batch data.power data.items self
    optimized tail next template

def reference : List (Result Input) → Slice field.QM31 → Result (Slice field.QM31)
  | [],weights => .ok weights
  | input::tail,weights => do
    let data ← input
    let next ← referenceUpdates data.power data.items weights
    reference tail next

theorem batches_eq (inputs : List (Result Input)) (self : verifier.BatchedWeights)
    (template : Slice field.QM31) (hg : Good self [])
    (hlen : template.val.length = self.raw.val.length)
    (hcount : self.terms.val+inputs.length ≤ 22)
    (hadmit : ∀ data,Result.ok data ∈ inputs → Admitted data self.raw.val.length) :
    optimized inputs self template = reference inputs (canonicalSlice self) := by
  induction inputs generalizing self with
  | nil =>
    exact CuSavingsRhoSourceFinish.source_success self template hlen
  | cons input tail ih =>
    cases input with
    | fail error => rfl
    | div => rfl
    | ok data =>
      have ha := hadmit data (by simp only [List.mem_cons,true_or])
      obtain ⟨out,hrun,href,hterms,hlength,hgood⟩ := batch_success data.items self data.power
        hg ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1 ha.2.2.2.2 (by
          simp only [List.length_cons] at hcount
          omega)
      simp only [optimized,reference,bind_tc_ok,hrun,href]
      apply ih out hgood (hlen.trans hlength.symm)
      · simp only [List.length_cons] at hcount
        rw [hterms]
        omega
      · intro data hd
        rw [hlength]
        exact hadmit data (List.mem_cons_of_mem _ hd)

theorem initial_good (weights : Slice field.QM31)
    (hc : ∀ w ∈ weights.val,Canonical w) : Good (initialState weights) [] := by
  intro i hi j
  change RhoBound (wordAt ((weights.val.map initialRow)[i.val]'hi) j).val
    (0+if i.val ∈ [] then 1 else 0)
  rw [List.getElem_map]
  simp only [List.not_mem_nil,ite_false,Nat.add_zero]
  exact initial_bound _ (hc _ (List.getElem_mem (by
    simpa only [initialState,List.length_map] using hi))) j

theorem initial_projection (weights : Slice field.QM31)
    (hc : ∀ w ∈ weights.val,Canonical w) : canonicalSlice (initialState weights) = weights := by
  apply Subtype.ext
  change (weights.val.map initialRow).map canonicalValue = weights.val
  rw [List.map_map]
  calc
    _ = weights.val.map id := by
      apply List.map_congr_left
      intro w hw
      exact canonical_initial w (hc w hw)
    _ = weights.val := by simp only [List.map_id]

theorem initialized_eq (inputs : List (Result Input)) (weights : Slice field.QM31)
    (hc : ∀ w ∈ weights.val,Canonical w) (hcount : inputs.length ≤ 22)
    (hadmit : ∀ data,Result.ok data ∈ inputs → Admitted data weights.val.length) :
    optimized inputs (initialState weights) weights = reference inputs weights := by
  rw [batches_eq inputs (initialState weights) weights (initial_good weights hc)
    (by simp only [initialState,List.length_map])
    (by change (0#usize).val+inputs.length ≤ 22;have hz : (0#usize).val=0 := by scalar_tac
        simpa only [hz,Nat.zero_add] using hcount)
    (by intro data hd;simpa only [initialState,List.length_map] using hadmit data hd)]
  rw [initial_projection weights hc]

#print axioms batches_eq
#print axioms initial_good
#print axioms initial_projection
#print axioms initialized_eq
end AspisR1.CuSavingsRhoBatches
