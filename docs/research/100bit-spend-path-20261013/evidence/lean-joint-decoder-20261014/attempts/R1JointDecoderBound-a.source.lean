import R1JointDecoder

/-! Transfer a fixed-prefix answer bound through the joint decoder and its
deterministic metadata attachment. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointDecoderBound

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep

variable {M Cv O : Type} {L : Nat}

theorem continuation_bound (p : Params M Cv L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L) (c : Addr L)
    (q : Program (Addr L) State O)
    (bad : JointDecoder.Output M Cv L → Prop) (B : ℚ)
    (hfixed : ∀ as,
      as.length = (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).length →
      mean (fun b => mean (fun x => indicator (bad (JointDecoder.attach ctx
        (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as,
          (p.σ (ctx.records.length + 1) b, x)))))) ≤ B) :
    lazyMean q T (fun v => indicator (∃ out,
      bfollow (JointDecoder.output p T ctx) v.1 (QueryNextLaw.own p c)
        ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none)) T =
          some out ∧ bad out)) ≤ B := by
  calc
    lazyMean q T (fun v => indicator (∃ out,
      bfollow (JointDecoder.output p T ctx) v.1 (QueryNextLaw.own p c)
        ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none)) T =
          some out ∧ bad out))
        ≤ blaw (JointDecoder.output p T ctx) (fun out => indicator (bad out))
            (QueryNextLaw.own p c)
            ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none)) :=
      chainB (JointDecoder.output p T ctx) (fun out => indicator (bad out)) q T
        (QueryNextLaw.own p c)
        ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none))
    _ = pmean (fun as => mean (fun b => mean (fun x => indicator (bad
          (JointDecoder.attach ctx (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as,
            (p.σ (ctx.records.length + 1) b, x)))))))
          ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none)) := by
      exact JointDecoder.output_law p T ctx c (fun out => indicator (bad out))
    _ ≤ B := by
      apply pmean_le
      intro as has
      have hlen : as.length =
          (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).length := by
        simpa only [List.length_map] using has
      exact hfixed as hlen

theorem decoded_bound (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (q : Program (Addr L) State O)
    (bad : JointDecoder.Output M Cv L → Prop) (B : ℚ)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointDecoder.Output M Cv L)
    (hdecode : JointDecoder.decode p pubBytes tag semanticFuel openingFuel c T =
      some (own, pend, g))
    (hfixed : ∀ ctx,
      JointContext.parse p pubBytes tag semanticFuel openingFuel c T = some ctx →
      ∀ as, as.length =
        (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).length →
        mean (fun b => mean (fun x => indicator (bad (JointDecoder.attach ctx
          (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as,
            (p.σ (ctx.records.length + 1) b, x)))))) ≤ B) :
    lazyMean q T (fun v => indicator (∃ out,
      bfollow g v.1 own pend T = some out ∧ bad out)) ≤ B := by
  cases hparse : JointContext.parse p pubBytes tag semanticFuel openingFuel c T with
  | none =>
      simp [JointDecoder.decode, hparse] at hdecode
  | some ctx =>
      have hshape : (QueryNextLaw.own p c,
          (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none),
          JointDecoder.output p T ctx) = (own, pend, g) := by
        simpa only [JointDecoder.decode, hparse, Option.map_some] using hdecode
      cases hshape
      exact continuation_bound p T ctx c q bad B (hfixed ctx hparse)

#print axioms continuation_bound
#print axioms decoded_bound

end AspisR1.JointDecoderBound
end
