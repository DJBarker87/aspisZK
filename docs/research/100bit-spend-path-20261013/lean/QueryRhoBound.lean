import R1QueryNextBound
import R1RhoSamplerBound

/-! The 21-root rho exception bound for the local adaptive continuation.
Sampler correspondence is explicit, and the residual data and query list
are functions of the recovered background component only. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryRhoBound
open FS FS2 FS2.Duplex R0C.V3
open AspisCircleGroupOrder AspisR1.MatchingSupport
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv O K E : Type} {L : Nat}
variable [Field K] [Fintype K] [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) E]

def bad (iota : K →+* E) (rhoOf : Cv → K)
    (dataOf : QueryNextLaw.Recovered L → Data E)
    (queriesOf : QueryNextLaw.Recovered L → Fin 22 → Fin 262144)
    (out : QueryNextLaw.Recovered L × Chal Cv) : Prop :=
  rhoOf out.2.1 ∈ QueryResidualBridge.rhoBad iota (dataOf out.1) (queriesOf out.1)

theorem continuation_rho_bound (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (c : Addr L) (i : Nat) (q : Program (Addr L) State O)
    (input : State ≃ Fin (2^256)) (output : Fin (P^4) ≃ K)
    (rhoOf : Cv → K)
    (hsigma : ∀ b, rhoOf (p.σ i b) =
      output (R0C.ModuloCounting.reduce (by norm_num [P]) (input b)))
    (iota : K →+* E)
    (dataOf : QueryNextLaw.Recovered L → Data E)
    (queriesOf : QueryNextLaw.Recovered L → Fin 22 → Fin 262144) :
    lazyMean q T (fun v => indicator (∃ out,
      bfollow (QueryNextLaw.output p T endpoint i) v.1 (QueryNextLaw.own p c)
        ((QueryDecoder.missing p T endpoint).map fun b => (b, none)) T = some out ∧
      bad iota rhoOf dataOf queriesOf out)) ≤ RhoSamplerBound.rhoCap := by
  apply QueryNextBound.continuation_bound
  intro as _
  simp only [bad, hsigma, mean_const]
  exact RhoSamplerBound.modulo_bad_mass (by norm_num [P]) input output iota
    (dataOf (QueryDecoder.fromAnswers p T endpoint as))
    (queriesOf (QueryDecoder.fromAnswers p T endpoint as))

theorem continuation_rho_lt_two_neg_119 (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (c : Addr L) (i : Nat) (q : Program (Addr L) State O)
    (input : State ≃ Fin (2^256)) (output : Fin (P^4) ≃ K)
    (rhoOf : Cv → K)
    (hsigma : ∀ b, rhoOf (p.σ i b) =
      output (R0C.ModuloCounting.reduce (by norm_num [P]) (input b)))
    (iota : K →+* E)
    (dataOf : QueryNextLaw.Recovered L → Data E)
    (queriesOf : QueryNextLaw.Recovered L → Fin 22 → Fin 262144) :
    lazyMean q T (fun v => indicator (∃ out,
      bfollow (QueryNextLaw.output p T endpoint i) v.1 (QueryNextLaw.own p c)
        ((QueryDecoder.missing p T endpoint).map fun b => (b, none)) T = some out ∧
      bad iota rhoOf dataOf queriesOf out)) < 1 / (2^119 : ℚ) :=
  (continuation_rho_bound p T endpoint c i q input output rhoOf hsigma iota dataOf queriesOf).trans_lt
    RhoSamplerBound.rhoCap_lt_two_neg_119

#print axioms continuation_rho_bound
#print axioms continuation_rho_lt_two_neg_119
end AspisR1.QueryRhoBound
end
