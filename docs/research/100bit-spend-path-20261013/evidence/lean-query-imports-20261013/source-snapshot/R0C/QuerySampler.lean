import R0C.QuerySource

/-! A trace-preserving FS2 sampler for the retained q22 program. This supplies
the round program, not the missing retry-aware completing decoder or INJ.
Exhaustion is an Except.error and must be rejected by the outer verifier. -/
set_option autoImplicit false
namespace R0C.QuerySampler
open AspisV8R19 AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open MemoizedProgramLaw AdaptiveFirstReadLaw
open Q22SamplerProgram Q22SamplerInvariants R412LegalQueryEnumeration
open OracleResampling CausalFirstHitUnionBound
noncomputable section
attribute [local instance] Classical.propDecidable

def liftProgram {I A C : Type} : Program I A C → FS2.Sampler I A C
  | .done c => .done c
  | .ask i k => .ask i (fun a => liftProgram (k a))

theorem liftProgram_exact {I A C : Type} [DecidableEq I] [Inhabited A]
    (p : Program I A C) : (liftProgram p).toProgram = p := by
  induction p with
  | done c => rfl
  | ask i k ih =>
    simp only [liftProgram, FS2.Sampler.toProgram]
    congr 1
    funext a
    exact ih a

def sampler (s : State) : FS2.Sampler Bytes State Result := liftProgram (challengeProgram s)

theorem sampler_exact (s : State) : (sampler s).toProgram = challengeProgram s :=
  liftProgram_exact _

def querySet (xs : List Nat) : Finset (Fin (2^18)) :=
  xs.toFinset.image (fun x => ⟨x % (2^18), Nat.mod_lt _ (by positivity)⟩)

theorem querySet_enum (u : LegalQuery) :
    querySet (enumQuery u) = Finset.univ.image u.val := by
  ext i
  simp only [querySet, Finset.mem_image, List.mem_toFinset, enumQuery,
    List.mem_ofFn, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, ⟨j, rfl⟩, hx⟩
    exact ⟨j, by simpa only [Nat.mod_eq_of_lt (u.val j).isLt] using hx⟩
  · rintro ⟨j, rfl⟩
    exact ⟨(u.val j).val, ⟨j, rfl⟩, by simp only [Nat.mod_eq_of_lt (u.val j).isLt]⟩

theorem valid_querySet_card (xs : List Nat) (h : ResultValid (.ok xs)) :
    (querySet xs).card = 22 := by
  obtain ⟨u, hu, _⟩ := existsUnique_enumQuery xs h.1 h.2.1 h.2.2
  rw [← hu, querySet_enum, Finset.card_image_of_injective _ u.property, Finset.card_univ]
  exact Fintype.card_fin 22

theorem sampler_success_card (H : Bytes → State) (s : State) (xs : List Nat)
    (h : (eval H (sampler s).toProgram).2.1 = .ok xs) : (querySet xs).card = 22 := by
  have he := congrArg (fun p => (eval H p).2.1) (sampler_exact s)
  have hr : (challengeRun H s).2.1 = .ok xs :=
    (congrArg (fun v => v.2.1) (challenge_exact H s)).symm.trans (he.symm.trans h)
  have hv := challenge_result_valid H s
  rw [hr] at hv
  exact valid_querySet_card xs hv

/-- Errors have no successful subset event. -/
def acceptedSubset (M : Finset (Fin (2^18))) : Except Nat (List Nat) → Prop
  | .error _ => False
  | .ok xs => querySet xs ⊆ M

theorem acceptedSubset_test (M : Finset (Fin (2^18))) (r : Except Nat (List Nat)) :
    indicator (acceptedSubset M r) = QuerySource.containsOnly M r := by
  cases r with
  | error n => simp [acceptedSubset, QuerySource.containsOnly, indicator]
  | ok xs =>
    apply FS.indicator_iff
    simp [acceptedSubset, querySet, Finset.image_subset_iff]

theorem sampler_subset_le (s : State) (M : Finset (Fin (2^18))) :
    independentMean (sampler s).toProgram
      (fun v => indicator (acceptedSubset M v.2.1)) ≤
      (M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ) := by
  have he : (fun v : View Bytes State Result => indicator (acceptedSubset M v.2.1)) =
      (fun v => QuerySource.containsOnly M v.2.1) := by
    funext v
    exact acceptedSubset_test M v.2.1
  rw [he, sampler_exact]
  exact QuerySource.successful_subset_le s M

theorem loop_reads_le (H : Bytes → State) (n : Nat) (s : State) (q : Q22WordScan.ScanState) :
    (loopRun H n s q).1.length ≤ 2*n := by
  induction n generalizing s q with
  | zero => simp [loopRun]
  | succ n ih =>
    simp only [loopRun]
    split_ifs
    · simp [calls]
    · simp only [List.length_append, calls, List.length_cons, List.length_nil]
      have h := ih (step H s).2 (Q22WordScan.scan q (SamplerWords.words 18 (step H s).1)).1
      omega
    · simp

/-- Sixteen calls includes both squeeze and advance for each of eight blocks;
this is a bound on all reads, so also bounds distinct first reads. -/
theorem sampler_reads_le (H : Bytes → State) (s : State) :
    (eval H (sampler s).toProgram).1.length ≤ 16 := by
  rw [sampler_exact, challenge_exact]
  exact loop_reads_le H 8 s ⟨[],0⟩

#print axioms liftProgram_exact
#print axioms sampler_success_card
#print axioms sampler_subset_le
#print axioms sampler_reads_le
end
end R0C.QuerySampler
