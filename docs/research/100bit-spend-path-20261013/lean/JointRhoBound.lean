import R1JointNextBound
import R1RhoSamplerBound

/-! The rho exception bound for the joint completed-prefix/query output under
the same explicit residual-data and sampler premises as the query-only bound. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointRhoBound

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
    (dataOf : JointNextLaw.Completed M Cv L → Data E)
    (queriesOf : JointNextLaw.Completed M Cv L → Fin 22 → Fin 262144)
    (out : JointNextLaw.Completed M Cv L × Chal Cv) : Prop :=
  rhoOf out.2.1 ∈ QueryResidualBridge.rhoBad iota (dataOf out.1) (queriesOf out.1)

theorem continuation_rho_bound (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (c : Addr L) (i : Nat)
    (q : Program (Addr L) State O)
    (input : State ≃ Fin (2^256)) (output : Fin (P^4) ≃ K)
    (rhoOf : Cv → K)
    (hsigma : ∀ b, rhoOf (p.σ i b) =
      output (R0C.ModuloCounting.reduce (by norm_num [P]) (input b)))
    (iota : K →+* E)
    (dataOf : JointNextLaw.Completed M Cv L → Data E)
    (queriesOf : JointNextLaw.Completed M Cv L → Fin 22 → Fin 262144) :
    lazyMean q T (fun v => indicator (∃ out,
      bfollow (JointNextLaw.output p T rs endpoint i) v.1 (QueryNextLaw.own p c)
        ((JointPrefixAnswers.missing p T rs endpoint).map fun b => (b, none)) T = some out ∧
      bad iota rhoOf dataOf queriesOf out)) ≤ RhoSamplerBound.rhoCap := by
  apply JointNextBound.continuation_bound
  intro as _
  simp only [bad, hsigma, mean_const]
  exact RhoSamplerBound.modulo_bad_mass (by norm_num [P]) input output iota
    (dataOf (JointPrefixAnswers.fromAnswers p T rs endpoint as))
    (queriesOf (JointPrefixAnswers.fromAnswers p T rs endpoint as))

theorem continuation_rho_lt_two_neg_119 (p : Params M Cv L)
    (T : Table (Addr L) State) (rs : List (Rec M)) (endpoint : State)
    (c : Addr L) (i : Nat) (q : Program (Addr L) State O)
    (input : State ≃ Fin (2^256)) (output : Fin (P^4) ≃ K)
    (rhoOf : Cv → K)
    (hsigma : ∀ b, rhoOf (p.σ i b) =
      output (R0C.ModuloCounting.reduce (by norm_num [P]) (input b)))
    (iota : K →+* E)
    (dataOf : JointNextLaw.Completed M Cv L → Data E)
    (queriesOf : JointNextLaw.Completed M Cv L → Fin 22 → Fin 262144) :
    lazyMean q T (fun v => indicator (∃ out,
      bfollow (JointNextLaw.output p T rs endpoint i) v.1 (QueryNextLaw.own p c)
        ((JointPrefixAnswers.missing p T rs endpoint).map fun b => (b, none)) T = some out ∧
      bad iota rhoOf dataOf queriesOf out)) < 1 / (2^119 : ℚ) :=
  (continuation_rho_bound p T rs endpoint c i q input output rhoOf hsigma iota dataOf queriesOf).trans_lt
    RhoSamplerBound.rhoCap_lt_two_neg_119

#print axioms continuation_rho_bound
#print axioms continuation_rho_lt_two_neg_119

end AspisR1.JointRhoBound
end
