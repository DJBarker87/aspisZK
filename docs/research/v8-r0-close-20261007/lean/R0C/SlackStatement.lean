import R0FS.V2

/-! A1: statement only. See FS_LOG for the rule recorded before this file.
The scaled law remains a total deterministic sampler law; bounded q22
success/error semantics does not instantiate its queryCard clause. -/
set_option autoImplicit false
namespace R0C.SlackStatement
open FS R0FS
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8R19.SourceDuplexStep AspisV8R19.DuplexFrames
noncomputable section

variable {E : Type} [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod AspisCircleGroupOrder.P) E] {Sfield : Fin 29 → Subfield E}
  {Pf I B : Type} {Kw : Nat}

structure SamplerLawsSlack [Fintype B] (δ : ℚ) (p : Params E Sfield Pf I B Kw) : Prop where
  nonzero : ∀ a, ∃ c, p.sampler 0 a = .field c ∧ c ≠ 0
  gamma : ∀ c : E, mean (fun a : Fin (p.k 0) → B => indicator (p.sampler 0 a = .field c)) ≤
    (1+δ) / ((Fintype.card E : ℚ) - 1)
  kappa : ∀ c : E, mean (fun a : Fin (p.k 1) → B => indicator (p.sampler 1 a = .field c)) ≤
    (1+δ) / (Fintype.card E : ℚ)
  tau : ∀ c : E, mean (fun a : Fin (p.k 2) → B => indicator (p.sampler 2 a = .field c)) ≤
    (1+δ) / (Fintype.card E : ℚ)
  alpha : ∀ c : E, mean (fun a : Fin (p.k 3) → B => indicator (p.sampler 3 a = .field c)) ≤
    (1+δ) / (Fintype.card E : ℚ)
  queryCard : ∀ a, ∃ S, p.sampler 4 a = .set S ∧ S.card = 22
  queries : ∀ M : Finset (Fin 262144),
    mean (fun a : Fin (p.k 4) → B =>
      indicator (∃ S, p.sampler 4 a = .set S ∧ S.card = 22 ∧ S ⊆ M)) ≤
    (1+δ) * ((M.card.choose 22 : ℚ) / (Nat.choose 262144 22 : ℚ))


/-- Requested conservative scaling, including the query row. -/
def epsilonSlack (E : Type) [Fintype E] (δ : ℚ) (i : Nat) : ℚ :=
  (1+δ) * R0FS.ε E i

def rbSlack (p : Params E Sfield Pf I B Kw) (δ : ℚ) :
    RoundByRound (Stmt E Sfield) (Msg E) (R0FS.Chal E) I B Kw :=
  { R0FS.roundByRound p with ε := epsilonSlack E δ }

def SamplerLawsSlackD {L : Nat}
    (δ : ℚ) (p : FS2.Duplex.Params (Msg E) (R0FS.Chal E) L)
    (msg : Pf → Nat → Msg E) : Prop :=
  SamplerLawsSlack δ (R0FS.V2.params1 (Sfield := Sfield) p msg)

def rb2Slack {L : Nat} (δ : ℚ) :
    FS2.RoundByRound' (Stmt E Sfield) (Msg E)
      (FS2.Duplex.Chal (R0FS.Chal E)) (FS2.Duplex.Addr L) State :=
  { R0FS.V2.rb2 with ε := epsilonSlack E δ }

def delta0 : ℚ :=
  257 * (AspisCircleGroupOrder.P^8 : ℚ) / (256^32 : ℚ) - 1

end
end R0C.SlackStatement
