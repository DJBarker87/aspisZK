import R1JointContext
import R1JointNextLaw
import R1BackgroundOutputMap
import R1BackgroundLawMap

/-! Address/table-only completing decoder for the ordinary-prefix/query/next
component. C1 and both checked messages are preserved in the output. This
structured component is not yet the full protocol's Prefix/message/challenge
representation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.JointDecoder
open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.CausalFirstHitUnionBound AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

abbrev Output (M Cv : Type) (L : Nat) :=
  State × M × M × (JointNextLaw.Completed M Cv L × Chal Cv)

abbrev Completion (M Cv : Type) (L : Nat) :=
  BS (Addr L) State State × List (Addr L × Option State) ×
    (State → List State → Output M Cv L)

def attach (ctx : JointContext.Context M L)
    (out : JointNextLaw.Completed M Cv L × Chal Cv) : Output M Cv L :=
  (ctx.c1, ctx.queryMessage, ctx.nextMessage, out)

def output (p : Params M Cv L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L) (x : State) (as : List State) : Output M Cv L :=
  attach ctx (JointNextLaw.output p T ctx.records ctx.endpoint
    (ctx.records.length + 1) x as)

def decode (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State) :
    Option (Completion M Cv L) :=
  (JointContext.parse p pubBytes tag semanticFuel openingFuel c T).map fun ctx =>
    (QueryNextLaw.own p c,
      (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none),
      output p T ctx)

theorem decode_of_parse (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (semanticFuel openingFuel : Nat) (c : Addr L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L)
    (h : JointContext.parse p pubBytes tag semanticFuel openingFuel c T = some ctx) :
    decode p pubBytes tag semanticFuel openingFuel c T =
      some (QueryNextLaw.own p c,
        (JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none),
        output p T ctx) := by
  simp only [decode, h, Option.map_some]

theorem follows_of_joint (p : Params M Cv L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L) (c : Addr L) (tr : List (Addr L × State))
    (out : JointNextLaw.Completed M Cv L × Chal Cv)
    (h : bfollow (JointNextLaw.output p T ctx.records ctx.endpoint (ctx.records.length + 1))
      tr (QueryNextLaw.own p c)
      ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none)) T =
        some out) :
    bfollow (output p T ctx) tr (QueryNextLaw.own p c)
      ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none)) T =
        some (attach ctx out) := by
  have hm := BackgroundOutputMap.bfollow_map (attach ctx)
    (JointNextLaw.output p T ctx.records ctx.endpoint (ctx.records.length + 1))
    tr (QueryNextLaw.own p c)
    ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none)) T
  rw [h] at hm
  exact hm

theorem output_law (p : Params M Cv L) (T : Table (Addr L) State)
    (ctx : JointContext.Context M L) (c : Addr L) (obs : Output M Cv L → ℚ) :
    blaw (output p T ctx) obs (QueryNextLaw.own p c)
        ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none)) =
      pmean (fun as => mean (fun b => mean (fun x =>
        obs (attach ctx (JointPrefixAnswers.fromAnswers p T ctx.records ctx.endpoint as,
          (p.σ (ctx.records.length + 1) b, x))))))
        ((JointPrefixAnswers.missing p T ctx.records ctx.endpoint).map fun b => (b, none)) := by
  unfold output
  rw [BackgroundLawMap.blaw_map]
  exact JointNextLaw.background_law p T ctx.records ctx.endpoint c (ctx.records.length + 1)
    (fun out => obs (attach ctx out))

#print axioms decode_of_parse
#print axioms follows_of_joint
#print axioms output_law
end AspisR1.JointDecoder
end
