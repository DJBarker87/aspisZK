import GSScalarAtCursorM10
import RRConcreteWriterM10

/-! Deterministic RR mirror with its actual outer fresh-tape cursor and
complete scalar arithmetic occurrence list. Pure child normalization uses the
maintained implementation; its separate counted mirror is already available.
No zero-work assertion about that normalization is made here. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RRActualScalarTraceM10
open CompPoly RRConcreteState RRConcreteValidState RRConcreteTraversal
open GSScalarCallScheduleM10
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open SequentialFreshProgram SequentialProgramInvariants
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

abbrev Result (K : Type) [Field K] [BEq K] [LawfulBEq K] :=
  (Option (List (List K)) × Nat) × List (Call K)

def children (ell q t : Nat) (H : Nat → Fin t → K × K)
    (s : ValidState ell K) (cursor : Nat) :
    (Option (List (K × ValidState ell K)) × Nat) × List (Call K) :=
  let r := GSScalarAtCursorM10.general (scalarPolynomial s.val) q t H cursor
  ((r.1.1.map (fun roots => roots.map (fun a => (a,child ell s a))),r.1.2),r.2)

theorem children_value (ell q t : Nat) (H : Nat → Fin t → K × K)
    (s : ValidState ell K) (cursor : Nat) :
    (children ell q t H s cursor).1 =
      (eval H (sequential (RRConcreteTraversal.children ell s q t) cursor)).2 := by
  have h := congrArg (fun r : Option (List K) × Nat =>
    (r.1.map (fun roots => roots.map (fun a => (a,child ell s a))),r.2))
    (GSScalarAtCursorM10.value (scalarPolynomial s.val) q t H cursor)
  simpa only [children,RRConcreteTraversal.children,sequential_bind,eval_bind,
    sequential,eval] using h

def walk {S : Type} (run : S → Nat → Result K) : List (K × S) → Nat → Result K
  | [],cursor => ((some [],cursor),[])
  | (a,s)::xs,cursor =>
    let r := run s cursor
    match r.1.1 with
    | none => ((none,r.1.2),r.2)
    | some ys =>
      let rest := walk run xs r.1.2
      ((rest.1.1.map (fun zs => ys.map (a::·)++zs),rest.1.2),r.2++rest.2)

theorem walk_value {S A : Type} (H : Nat → A)
    (run : S → Nat → Result K)
    (p : S → Program Nat A (Option (List (List K))))
    (hv : ∀ s c, (run s c).1 = (eval H (sequential (p s) c)).2)
    (xs : List (K × S)) (cursor : Nat) :
    (walk run xs cursor).1 =
      (eval H (sequential (RRProgramTraversal.walkChildren p xs) cursor)).2 := by
  induction xs generalizing cursor with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨a,s⟩
    simp only [walk,RRProgramTraversal.walkChildren,RRProgramTraversal.optionBind,
      sequential_bind,eval_bind]
    rw [← hv]
    cases ho : (run s cursor).1.1 with
    | none => rfl
    | some ys =>
      simp only [RRProgramTraversal.mapOption,sequential_bind,eval_bind]
      rw [← ih]
      cases hr : (walk run xs (run s cursor).1.2).1.1 <;> rfl

def collect (ell q t : Nat) (H : Nat → Fin t → K × K) :
    Nat → ValidState ell K → Nat → Result K
  | 0,s,cursor => ((some (if zeroTest s.val then [[]] else []),cursor),[])
  | d+1,s,cursor =>
    let r := children ell q t H s cursor
    match r.1.1 with
    | none => ((none,r.1.2),r.2)
    | some cs =>
      let rest := walk (collect ell q t H d) cs r.1.2
      (rest.1,r.2++rest.2)

theorem value (ell q t : Nat) (H : Nat → Fin t → K × K)
    (d : Nat) (s : ValidState ell K) (cursor : Nat) :
    (collect ell q t H d s cursor).1 =
      (eval H (sequential (RRConcreteTraversal.run ell q t d s) cursor)).2 := by
  induction d generalizing s cursor with
  | zero => rfl
  | succ d ih =>
    simp only [collect,RRConcreteTraversal.run,RRProgramTraversal.collectProgram,
      RRProgramTraversal.optionBind,sequential_bind,eval_bind]
    rw [← children_value]
    cases ho : (children ell q t H s cursor).1.1 with
    | none => rfl
    | some cs =>
      exact walk_value H (collect ell q t H d) (RRConcreteTraversal.run ell q t d)
        ih cs (children ell q t H s cursor).1.2

#print axioms children_value
#print axioms walk_value
#print axioms value
end AspisR1.RRActualScalarTraceM10
end
