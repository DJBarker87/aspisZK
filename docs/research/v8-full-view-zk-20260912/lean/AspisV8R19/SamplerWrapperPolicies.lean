import AspisV8R19.BoundedSamplerWrapper

/-! Literal cap-three nonzero/OOD wrapper policies. Error constructors are
kept separate where Rust separates them, not turned into successful defaults. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerWrapperPolicies
open DuplexFrames SourceDuplexStep MemoizedProgramLaw BoundedSamplerWrapper

inductive Error where
  | challengeExhausted
  | subfieldExhausted
  | parameterExhausted
  deriving DecidableEq, Repr

def nonzeroAccept (xs : List Nat) : Option (List Nat) :=
  if xs = [0,0,0,0] then none else some xs

def oodAccept : List Nat → Option (List Nat)
  | [a,b,c,d] => if c = 0 ∧ d = 0 then none else some [a,b,c,d]
  | _ => none

def nonzeroProgram (s : State) :=
  program nonzeroAccept Error.challengeExhausted Error.challengeExhausted 3 s
def nonzeroRun (H : Bytes → State) (s : State) :=
  run nonzeroAccept Error.challengeExhausted Error.challengeExhausted H 3 s
def oodProgram (s : State) :=
  program oodAccept Error.challengeExhausted Error.subfieldExhausted 3 s
def oodRun (H : Bytes → State) (s : State) :=
  run oodAccept Error.challengeExhausted Error.subfieldExhausted H 3 s

theorem nonzero_exact (H : Bytes → State) (s : State) :
    eval H (nonzeroProgram s) = nonzeroRun H s := exact_run _ _ _ H 3 s
theorem ood_exact (H : Bytes → State) (s : State) :
    eval H (oodProgram s) = oodRun H s := exact_run _ _ _ H 3 s
theorem nonzero_law (s : State) :
    SamplerOracleLaws.CorrectLaw (nonzeroProgram s) (fun H => nonzeroRun H s) :=
  oracle_law _ _ _ 3 s
theorem ood_law (s : State) :
    SamplerOracleLaws.CorrectLaw (oodProgram s) (fun H => oodRun H s) :=
  oracle_law _ _ _ 3 s

theorem nonzero_policy (xs ys : List Nat) (h : nonzeroAccept xs = some ys) :
    xs = ys ∧ ys ≠ [0,0,0,0] := by
  by_cases hz : xs = [0,0,0,0]
  · simp [nonzeroAccept,hz] at h
  · have he : xs = ys := by simpa [nonzeroAccept,hz] using h
    exact ⟨he,he ▸ hz⟩

theorem ood_policy (xs ys : List Nat) (h : oodAccept xs = some ys) :
    xs = ys ∧ ∃ a b c d, ys = [a,b,c,d] ∧ ¬ (c = 0 ∧ d = 0) := by
  unfold oodAccept at h
  split at h
  · rename_i a b c d
    by_cases hz : c = 0 ∧ d = 0
    · simp [hz] at h
    · have he : [a,b,c,d] = ys := by simpa [hz] using h
      exact ⟨he,a,b,c,d,he.symm,hz⟩
  · simp at h

theorem nonzero_result (H : Bytes → State) (s : State) (ys : List Nat)
    (h : (nonzeroRun H s).2.1 = .ok ys) :
    ys.length = 4 ∧ (∀ a ∈ ys, a < 2147483647) ∧ ys ≠ [0,0,0,0] := by
  obtain ⟨xs,hlen,hcan,ha⟩ := successful_image _ _ _ H 3 s ys h
  obtain ⟨rfl,hne⟩ := nonzero_policy xs ys ha
  exact ⟨hlen,hcan,hne⟩

theorem ood_result (H : Bytes → State) (s : State) (ys : List Nat)
    (h : (oodRun H s).2.1 = .ok ys) :
    (∀ a ∈ ys, a < 2147483647) ∧ ∃ a b c d,
      ys = [a,b,c,d] ∧ ¬ (c = 0 ∧ d = 0) := by
  obtain ⟨xs,_,hcan,ha⟩ := successful_image _ _ _ H 3 s ys h
  obtain ⟨rfl,hw⟩ := ood_policy xs ys ha
  exact ⟨hcan,hw⟩

#print axioms nonzero_exact
#print axioms ood_exact
#print axioms nonzero_law
#print axioms ood_law
#print axioms nonzero_policy
#print axioms ood_policy
#print axioms nonzero_result
#print axioms ood_result
end AspisV8R19.SamplerWrapperPolicies
