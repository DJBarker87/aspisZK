import RRProgramTraversal
import RRFixedTapeRecovery

/-! RR candidates are actual length-d coefficient lists, including padded
zero tails. The semantic degree bound alone would not imply this fact. -/
set_option autoImplicit false
namespace AspisR1.RRCandidateShapeM10
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SequentialProgramInvariants RRProgramTraversal
variable {I A K S : Type}

def Shape (d : Nat) (out : Option (List (List K))) : Prop :=
  ∀ cs, out = some cs → ∀ xs ∈ cs, xs.length = d

theorem walk_shape (run : S → Program I A (Option (List (List K))))
    (d : Nat) (h : ∀ s, AllOutcomes (run s) (Shape d)) (xs : List (K × S)) :
    AllOutcomes (walkChildren run xs) (Shape (d+1)) := by
  induction xs with
  | nil => intro cs hc; cases hc; simp
  | cons x xs ih =>
    rcases x with ⟨a,s⟩
    apply all_bind
    apply all_mono _ (h s)
    intro out ho
    cases hv : out with
    | none => intro cs hc; cases hc
    | some ys =>
      apply all_bind
      apply all_mono _ ih
      intro out hz
      cases hw : out with
      | none => intro cs hc; cases hc
      | some zs =>
        intro cs hc
        cases hc
        intro v hm
        rcases List.mem_append.mp hm with hm | hm
        · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hm
          simp only [List.length_cons, ho ys hv u hu]
        · exact hz zs hw v hm

theorem collect_shape (zeroTest : S → Bool)
    (children : S → Program I A (Option (List (K × S)))) (d : Nat) (s : S) :
    AllOutcomes (collectProgram zeroTest children d s) (Shape d) := by
  induction d generalizing s with
  | zero =>
    intro cs hc
    cases hc
    cases zeroTest s <;> simp
  | succ d ih =>
    apply all_bind
    have htrue : AllOutcomes (children s) (fun _ => True) := by
      induction children s with
      | done _ => trivial
      | ask _ _ ih => exact ih
    apply all_mono _ htrue
    intro out _
    cases out with
    | none => intro cs hc; cases hc
    | some cs => exact walk_shape _ d ih cs

theorem fixed_recover_shape {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]
    (ell q t d : Nat) (s : RRConcreteState.RawState F)
    (hd : ∀ i ≤ s.maxX, (RRVectorRowPolynomialBridge.inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : RRConcreteState.model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range (d*ell)} → Fin t → F × F) :
    Shape d (RRFixedTapeRecovery.recover ell q t d s hd hn H).1 := by
  exact all_eval _ _ _ (all_sequential _ _
    (collect_shape (fun u => RRConcreteState.zeroTest u.val)
      (fun u => RRConcreteTraversal.children ell u q t) d
      (RRConcreteInitialValidStateFromFacts.initialValidState ell s hd hn)) 0)

#print axioms walk_shape
#print axioms collect_shape
#print axioms fixed_recover_shape
end AspisR1.RRCandidateShapeM10
