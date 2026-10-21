import R1Z.ProverCommitProduct25
/-! A RunJoin for the complete finite rejection component with arbitrary
retained model state and arbitrary continuation output. The seed and independent
fuel have the exact deployed RunJoin carrier. Identifying the shipped shared
oracle execution with this component remains a separate source obligation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitProductRun25
open R0Z R0Z.FsStatement R0Z.FsAbort R0Z.LawTransport
open ProverCommitFuelMass22 ProverCommitFuelJoin22 ProverCommitProduct25
open R1Z.CouplingR1PBin
attribute [local instance] Classical.propDecidable
abbrev Coins := Fin count → NZ (0 : OracleAnswer)
abbrev Model (Rest : Type) := Coins × Rest
abbrev Space (Rest : Type) := ((Model Rest × OracleAnswer) × Tape)
abbrev Source (Rest : Type) := (Tape × Rest) × OracleAnswer

def exchange {Rest : Type} (s : Space Rest) : Space Rest :=
  let q := fun i => swap (0 : OracleAnswer) k (s.1.1.1 i,s.2 i)
  ((((fun i => (q i).1),s.1.1.2),s.1.2),fun i => (q i).2)

theorem exchange_involution {Rest : Type} (s : Space Rest) :
    exchange (exchange s) = s := by
  rcases s with ⟨⟨⟨coins,rest⟩,seed⟩,tape⟩
  have h : ∀ i, swap (0 : OracleAnswer) k
      ((swap (0 : OracleAnswer) k (coins i,tape i)).1,
       (swap (0 : OracleAnswer) k (coins i,tape i)).2) = (coins i,tape i) := by
    intro i
    simpa only [Prod.mk.eta] using swap_involution (0 : OracleAnswer) k (coins i,tape i)
  apply Prod.ext
  · apply Prod.ext
    · apply Prod.ext
      · funext i
        exact congrArg Prod.fst (h i)
      · rfl
    · rfl
  · funext i
    exact congrArg Prod.snd (h i)

def exchangeEquiv (Rest : Type) : Space Rest ≃ Space Rest where
  toFun := exchange
  invFun := exchange
  left_inv := exchange_involution
  right_inv := exchange_involution

def regroup (Rest : Type) : Space Rest ≃ (Coins × Source Rest) where
  toFun s := (s.1.1.1,((s.2,s.1.1.2),s.1.2))
  invFun s := (((s.1,s.2.1.2),s.2.2),s.2.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Exact source randomness: all 24 five-word raw tapes, the unchanged rest
of the model randomness, and the retained seed. No output equality is used. -/
theorem source_marginal {Rest : Type} [Fintype Rest] :
    MP (fun s : Space Rest => (regroup Rest (exchange s)).2) := by
  intro test
  exact (mp_equiv (exchangeEquiv Rest) (fun s => test (regroup Rest s).2)).trans
    ((mp_equiv (regroup Rest) (fun p => test p.2)).trans (mp_snd test))

def cp (Rest : Type) [Fintype Rest] [Nonempty Rest] :
    Coupling (Source Rest) (Space Rest) where
  S := Space Rest
  finS := inferInstance
  nonemptyS := inferInstance
  toR := fun s => (regroup Rest (exchange s)).2
  toM := id
  meanR := source_marginal
  meanM := fun _ => rfl

/-- The entire model's product marginal, including the independent tape,
is retained verbatim. -/
theorem model_marginal (Rest : Type) [Fintype Rest] [Nonempty Rest]
    (test : Space Rest → ℚ) :
    mean (fun s : (cp Rest).S => test ((cp Rest).toM s)) = mean test := rfl

def runtime {Rest V : Type} (next : (Fin count → Option OracleAnswer) → Rest → V)
    (r : Source Rest) : V := next (fun i => first (0 : OracleAnswer) (r.1.1 i)) r.1.2

def model {Rest V : Type} (next : (Fin count → Option OracleAnswer) → Rest → V)
    (m : Model Rest) : V := next (fun i => some (m.1 i).val) m.2

/-- A genuine RunJoin for this rejection component. Arbitrary continuations
may retain values, decision, state and observable history. The independent
seed/fuel law is proved rather than supplied as a record field hypothesis. -/
def runJoin {Rest V : Type} [Fintype Rest] [Nonempty Rest]
    (next : (Fin count → Option OracleAnswer) → Rest → V)
    (old : Fin 8 → Model Rest → Prop)
    (queries : Model Rest → List ProverCommitSeedEvent19.Entry) :
    RunJoin (runtime next) (model next) old queries where
  cp := cp Rest
  agreement := by
    intro s good
    have no_failure : ∀ i, ¬ failure i s.2 := by
      intro i hi
      exact good ⟨0,Or.inr ⟨rfl,i,hi⟩⟩
    have answers : (fun i => first (0 : OracleAnswer)
        (swap (0 : OracleAnswer) k (s.1.1.1 i,s.2 i)).2) =
        (fun i => some (s.1.1.1 i).val) := by
      funext i
      rw [first_swap]
      exact if_neg (no_failure i)
    change next (fun i => first (0 : OracleAnswer)
      (swap (0 : OracleAnswer) k (s.1.1.1 i,s.2 i)).2) s.1.1.2 = _
    rw [answers]
    rfl

#print axioms exchange_involution
#print axioms source_marginal
#print axioms cp
#print axioms model_marginal
#print axioms runJoin
end R1Z.ProverCommitProductRun25
