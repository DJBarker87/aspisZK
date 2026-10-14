import R1QueryNextLaw

/-! Reuse of the existing background-chain bound for an arbitrary adaptive
continuation program. The fixed-completion error bound remains explicit. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.QueryNextBound
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv O : Type} {L : Nat}

theorem continuation_bound (p : Params M Cv L) (T : Table (Addr L) State)
    (endpoint : State) (c : Addr L) (i : Nat)
    (q : Program (Addr L) State O)
    (bad : QueryNextLaw.Recovered L × Chal Cv → Prop) (B : ℚ)
    (hfixed : ∀ as, as.length = (QueryDecoder.missing p T endpoint).length →
      mean (fun b => mean (fun x => indicator
        (bad (QueryDecoder.fromAnswers p T endpoint as, (p.σ i b, x)))))) ≤ B) :
    lazyMean q T (fun v => indicator (∃ out,
      bfollow (QueryNextLaw.output p T endpoint i) v.1 (QueryNextLaw.own p c)
        ((QueryDecoder.missing p T endpoint).map fun b => (b, none)) T = some out ∧
      bad out)) ≤ B := by
  exact le_trans
    (chainB (QueryNextLaw.output p T endpoint i) bad q T (QueryNextLaw.own p c)
      ((QueryDecoder.missing p T endpoint).map fun b => (b, none)))
    (QueryNextLaw.background_bound p T endpoint c i (fun out => indicator (bad out)) B hfixed)

#print axioms continuation_bound
end AspisR1.QueryNextBound
end
