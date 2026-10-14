import R1JointNextLaw

/-! Apply the existing background-chain bound to an arbitrary continuation
for the jointly completed prefix and recovered query. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointNextBound

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv O : Type} {L : Nat}

theorem continuation_bound (p : Params M Cv L) (T : Table (Addr L) State)
    (rs : List (Rec M)) (endpoint : State) (c : Addr L) (i : Nat)
    (q : Program (Addr L) State O)
    (bad : JointNextLaw.Completed M Cv L × Chal Cv → Prop) (B : ℚ)
    (hfixed : ∀ as, as.length = (JointPrefixAnswers.missing p T rs endpoint).length →
      mean (fun b => mean (fun x => indicator
        (bad (JointPrefixAnswers.fromAnswers p T rs endpoint as, (p.σ i b, x))))) ≤ B) :
    lazyMean q T (fun v => indicator (∃ out,
      bfollow (JointNextLaw.output p T rs endpoint i) v.1 (QueryNextLaw.own p c)
        ((JointPrefixAnswers.missing p T rs endpoint).map fun b => (b, none)) T = some out ∧
      bad out)) ≤ B := by
  exact le_trans
    (chainB (JointNextLaw.output p T rs endpoint i) bad q T (QueryNextLaw.own p c)
      ((JointPrefixAnswers.missing p T rs endpoint).map fun b => (b, none)))
    (JointNextLaw.background_bound p T rs endpoint c i
      (fun out => indicator (bad out)) B hfixed)

#print axioms continuation_bound

end AspisR1.JointNextBound
end
