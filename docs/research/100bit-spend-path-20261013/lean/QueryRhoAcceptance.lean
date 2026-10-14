import R1QueryRhoBound
import R1RhoAcceptance

/-! Accepted query misses are contained in the existing rho exception event. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryRhoAcceptance

open FS FS2 FS2.Duplex R0C.V3
open AspisCircleGroupOrder AspisR1.MatchingSupport
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv O K E : Type} {L : Nat}
variable [Field K] [Fintype K] [Field E] [Fintype E] [DecidableEq E]
  [Algebra (ZMod P) K] [Algebra (ZMod P) E]

def bad (iota : K →+* E) (rhoOf : Cv → K)
    (dataOf : QueryNextLaw.Recovered L → Data E)
    (queriesOf : QueryNextLaw.Recovered L → Fin 22 → Fin 262144)
    (out : QueryNextLaw.Recovered L × Chal Cv) : Prop :=
  (∃ j, queriesOf out.1 j ∉ MatchingSupport.matchingSet (dataOf out.1)) ∧
    RhoAcceptance.AcceptedQueries iota (dataOf out.1) (queriesOf out.1) (rhoOf out.2.1)

theorem bad_implies_rho_bad (iota : K →+* E) (rhoOf : Cv → K)
    (dataOf : QueryNextLaw.Recovered L → Data E)
    (queriesOf : QueryNextLaw.Recovered L → Fin 22 → Fin 262144)
    (out : QueryNextLaw.Recovered L × Chal Cv)
    (hout : bad iota rhoOf dataOf queriesOf out) :
    QueryRhoBound.bad iota rhoOf dataOf queriesOf out := by
  rcases hout with ⟨hmiss, haccept⟩
  exact RhoAcceptance.accepted_mem_bad_of_query_miss iota
    (dataOf out.1) (queriesOf out.1) (rhoOf out.2.1) hmiss haccept

theorem continuation_accepted_miss_lt_two_neg_119
    (p : Params M Cv L) (T : Table (Addr L) State)
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
      bad iota rhoOf dataOf queriesOf out)) < 1 / (2^119 : ℚ) := by
  have hle : lazyMean q T (fun v => indicator (∃ out,
      bfollow (QueryNextLaw.output p T endpoint i) v.1 (QueryNextLaw.own p c)
        ((QueryDecoder.missing p T endpoint).map fun b => (b, none)) T = some out ∧
      bad iota rhoOf dataOf queriesOf out)) ≤
      lazyMean q T (fun v => indicator (∃ out,
        bfollow (QueryNextLaw.output p T endpoint i) v.1 (QueryNextLaw.own p c)
          ((QueryDecoder.missing p T endpoint).map fun b => (b, none)) T = some out ∧
        QueryRhoBound.bad iota rhoOf dataOf queriesOf out)) := by
    apply FS.lazyMean_mono
    intro v
    apply FS.indicator_mono
    rintro ⟨out, hf, hbad⟩
    exact ⟨out, hf, bad_implies_rho_bad iota rhoOf dataOf queriesOf out hbad⟩
  exact hle.trans_lt (QueryRhoBound.continuation_rho_lt_two_neg_119
    p T endpoint c i q input output rhoOf hsigma iota dataOf queriesOf)

#print axioms bad_implies_rho_bad
#print axioms continuation_accepted_miss_lt_two_neg_119

end AspisR1.QueryRhoAcceptance
end
