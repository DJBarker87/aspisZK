import RRProgramWalkRelation
import RRPrefixCollector

noncomputable section
namespace AspisR1.RRProgramRecoveryContracts
open Polynomial RRDenseCoeffVector RRRootDescent RRPrefixCollector
open AspisR1.RRProgramTraversal AspisR1.RRProgramWalkRelation
open AspisR1.SequentialProgramInvariants
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
variable {I A K S : Type} [Field K]

def CandidateResult (model : S → (K[X])[X]) (d : Nat)
    (s : S) (out : List (List K)) : Prop :=
  (∀ candidate ∈ out, (model s).eval (toPolynomial candidate) = 0) ∧
  ∀ f : K[X], (model s).eval f = 0 → (f = 0 ∨ f.natDegree < d) →
    ∃ candidate ∈ out, toPolynomial candidate = f

theorem walkResult_sound (model : S → (K[X])[X]) (parent : S) (d : Nat)
    (cs : List (K × S)) (out : List (List K))
    (hw : WalkResult (CandidateResult model d) cs out)
    (hstep : ∀ a t, (a,t) ∈ cs → ∀ f,
      (model t).eval f = 0 → (model parent).eval (C a + X*f) = 0) :
    ∀ candidate ∈ out, (model parent).eval (toPolynomial candidate) = 0 := by
  revert hstep
  induction hw with
  | nil => intro _ candidate hc; simp at hc
  | cons a s tail ys zs hhead hrest ih =>
    intro hstep candidate hc
    rcases List.mem_append.mp hc with hleft | hright
    · obtain ⟨suffix,hsuffix,heq⟩ := List.mem_map.mp hleft
      subst candidate
      rw [toPolynomial_cons]
      exact hstep a s (List.mem_cons_self ..) _ (hhead.1 suffix hsuffix)
    · exact ih (fun a t ht => hstep a t (List.mem_cons_of_mem _ ht)) candidate hright

theorem walkResult_complete_child (model : S → (K[X])[X]) (d : Nat)
    (cs : List (K × S)) (out : List (List K))
    (hw : WalkResult (CandidateResult model d) cs out)
    (a : K) (s : S) (hmem : (a,s) ∈ cs) (f : K[X])
    (hf : (model s).eval f = 0) (hbound : f = 0 ∨ f.natDegree < d) :
    ∃ candidate ∈ out, toPolynomial candidate = C a + X*f := by
  induction hw with
  | nil => simp at hmem
  | cons b t tail ys zs hhead hrest ih =>
    rcases List.mem_cons.mp hmem with heq | htail
    · cases heq
      obtain ⟨candidate,hcand,hpoly⟩ := hhead.2 f hf hbound
      refine ⟨b::candidate, List.mem_append_left _ (List.mem_map.mpr
        ⟨candidate,hcand,rfl⟩), ?_⟩
      rw [toPolynomial_cons, hpoly]
    · obtain ⟨candidate,hcand,hpoly⟩ := ih htail
      exact ⟨candidate,List.mem_append_right _ hcand,hpoly⟩

/-- Both recovery directions for the same aborting randomized traversal.
The local child contracts are required only on actual returned lists. The
degree-tail and reconstruction steps reuse the existing prefix collector. -/
theorem collectProgram_correct (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S))))
    (model : S → (K[X])[X])
    (hzero : ∀ s, zeroTest s = true ↔ (model s).eval 0 = 0)
    (hchildren : ∀ s, AllOutcomes (children s) (fun out => ∀ cs, out = some cs →
      (∀ a t, (a,t) ∈ cs → ∀ f,
        (model t).eval f = 0 → (model s).eval (C a + X*f) = 0) ∧
      (∀ f, (model s).eval f = 0 → ∃ a t, (a,t) ∈ cs ∧
        a = f.coeff 0 ∧ (model t).eval f.divX = 0)))
    (d : Nat) (s : S) :
    AllOutcomes (collectProgram zeroTest children d s)
      (fun out => ∀ candidates, out = some candidates → CandidateResult model d s candidates) := by
  induction d generalizing s with
  | zero =>
    intro candidates hs
    cases hs
    constructor
    · intro candidate hc
      by_cases hz : zeroTest s = true
      · simp only [hz, ↓reduceIte, List.mem_singleton] at hc
        subst candidate
        rw [toPolynomial_nil]
        exact (hzero s).mp hz
      · simp [hz] at hc
    · intro f hf hbound
      have hfzero : f = 0 := hbound.resolve_right (Nat.not_lt_zero _)
      subst f
      refine ⟨[], ?_, toPolynomial_nil⟩
      simp [(hzero s).mpr hf]
  | succ d ih =>
    rw [collectProgram, optionBind]
    apply all_bind
    apply all_mono _ (hchildren s)
    intro out hout
    cases out with
    | none => intro candidates hs; contradiction
    | some cs =>
      have hcs := hout cs rfl
      apply all_mono _ (walkChildren_all _ (CandidateResult model d) (fun u => ih u) cs)
      intro out hout candidates hs
      have hw := hout candidates hs
      refine ⟨walkResult_sound model s d cs candidates hw hcs.1, ?_⟩
      intro f hf hbound
      obtain ⟨a,t,hchild,ha,htailroot⟩ := hcs.2 f hf
      obtain ⟨candidate,hcand,hpoly⟩ := walkResult_complete_child model d cs candidates hw
        a t hchild f.divX htailroot (tail_degree_bound d f hbound)
      refine ⟨candidate,hcand,?_⟩
      rw [hpoly, ha, head_tail]

#print axioms CandidateResult
#print axioms walkResult_sound
#print axioms walkResult_complete_child
#print axioms collectProgram_correct
end AspisR1.RRProgramRecoveryContracts
