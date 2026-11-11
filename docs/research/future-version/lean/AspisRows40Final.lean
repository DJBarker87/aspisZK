import R1JointTranscriptView
import BackgroundCanonicalLabels
import AspisRows40Context
import AspisRows40Decoder

/-! Aspis one-transaction verifier: the completing decoder component of rows
33 to 39, its law, and its canonical-address lemma.

The component copies R1's row-32 component (`JointUnifiedDecoder.decode`,
`JointDecoder.decode`) one step further. From the absorb frame `c` of row n and
the table, `Context.parse` recovers R1's row-32 context and the frames and
messages of rows 32 .. n-1. The component then:
* reads its own row as R1's plain rows do: `QueryNextLaw.own p c` (the absorb
  answer, the squeeze spawned in the background, the advance);
* leaves pending R1's joint missing cells (`JointPrefixAnswers.missing`, rows
  0 .. 31) followed by the squeeze cells of rows 32 .. n-1 that are absent from
  the table and not already pending (`newMissing`);
* outputs the prefix: R1's 32-round prefix (`JointTranscriptView.mkPrefix` of
  `JointPrefixAnswers.fromAnswers`, exactly R1's row-32 output prefix), then
  rows 32 .. n-1 as payload rounds whose challenges are `p.σ j` of the squeeze
  answer (table, else pending) and the next frame's absorbed state; row n's
  message; and row n's challenge from the own squeeze and advance answers.

Law (`background_sampler_law`, copy of `JointUnifiedLaw.background_sampler_law`)
and bound (`decoded_bound`, copy of `JointUnifiedBound.decoded_bound`): the
background law of the decoded start is the pending-answer average of the
fixed-prefix sampler law of row n. Canonical addresses (`decode_good`, the
analogue of `UnifiedDecoderCanonical.decode_good` for this component). -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.Final
open FS FS2 FS2.Duplex R0C.V3
open AspisR1 AspisR1.TranscriptView
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.AdaptiveFirstReadLaw AspisV8R19.OracleResampling
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open BackgroundCanonicalLabels CanonicalByteAddress

variable {M Cv : Type} {L : Nat}

/-! ## Rows 32 .. n-1 of a parsed context -/

/-- The state an absorb frame absorbs into (its leading 32 bytes). -/
def frameState (a : Addr L) : State := ((parseAbsorb a).map fun r => r.1).getD default

/-- Absorb frames of rows 32 .. n-1. -/
def frames (ctx : Context.Context M L) : List (Addr L) := ctx.rhoAbsorb :: ctx.tail.map Prod.fst

/-- Messages of rows 32 .. n-1. -/
def messages (ctx : Context.Context M L) : List M := ctx.joint.nextMessage :: ctx.tail.map Prod.snd

/-- States after rows 32 .. n-1: the state the next frame absorbs into. -/
def nexts (ctx : Context.Context M L) : List State :=
  ctx.tail.map (fun t => frameState t.1) ++ [ctx.endpoint]

/-- Squeeze cells of rows 32 .. n-1 (at the table's answer of each frame). -/
def squeezes (p : Params M Cv L) (T : Table (Addr L) State) (ctx : Context.Context M L) :
    List (Addr L) :=
  (frames ctx).map fun a => squeezeA p ((T a).getD default)

def jointMissing (p : Params M Cv L) (T : Table (Addr L) State) (ctx : Context.Context M L) :
    List (Addr L) :=
  JointPrefixAnswers.missing p T ctx.joint.records ctx.joint.endpoint

def newMissing (p : Params M Cv L) (T : Table (Addr L) State) (ctx : Context.Context M L) :
    List (Addr L) :=
  ((squeezes p T ctx).filter fun c => (T c).isNone && !((jointMissing p T ctx).contains c)).dedup

def missing (p : Params M Cv L) (T : Table (Addr L) State) (ctx : Context.Context M L) :
    List (Addr L) :=
  jointMissing p T ctx ++ newMissing p T ctx

/-- Rounds 32 .. n-1 from (message, squeeze cell, next state) triples. -/
def laterRows (σ : Nat → State → Cv) (ans : Addr L → State) :
    Nat → List (M × Addr L × State) → List (M × Chal Cv)
  | _, [] => []
  | i, (m, sq, x) :: rest => (m, (σ i (ans sq), x)) :: laterRows σ ans (i + 1) rest

theorem laterRows_length (σ : Nat → State → Cv) (ans : Addr L → State) :
    ∀ (i : Nat) (xs : List (M × Addr L × State)), (laterRows σ ans i xs).length = xs.length := by
  intro i xs
  induction xs generalizing i with
  | nil => rfl
  | cons t rest ih =>
      obtain ⟨m, sq, x⟩ := t
      simp only [laterRows, List.length_cons, ih]

/-- The completed prefix for an answer list of the missing cells. -/
def prefixOf (p : Params M Cv L) (pub : UnifiedSampler.Public L) (T : Table (Addr L) State)
    (ctx : Context.Context M L) (as : List State) : UnifiedSampler.Prefix M Cv L :=
  let k := (jointMissing p T ctx).length
  let acc := R0C.V3.DQ.accFrom (missing p T ctx) as
  let P32 := JointTranscriptView.mkPrefix pub ctx.joint.c1 ctx.joint.queryMessage
    (JointPrefixAnswers.fromAnswers p T ctx.joint.records ctx.joint.endpoint (as.take k))
  ⟨pub, P32.rounds ++ later (laterRows p.σ (fun a => (T a).getD (acc a)) 32
    ((messages ctx).zip ((squeezes p T ctx).zip (nexts ctx))))⟩

def output (p : Params M Cv L) (pub : UnifiedSampler.Public L) (T : Table (Addr L) State)
    (n : Nat) (ctx : Context.Context M L) (x : State) (as : List State) :
    JointTranscriptView.Output M Cv L :=
  let N := (missing p T ctx).length
  (prefixOf p pub T ctx (as.take N), .payload ctx.message,
    liftChallenge (p.σ n ((as.drop N).headD default), x))

/-! ## The component -/

def decode (p : Params M Cv L) (pub : UnifiedSampler.Public L) (n : Nat) :
    Dec (UnifiedSampler.Public L) (Message M) (Challenge Cv) (Addr L) State State :=
  fun c T => (Context.parse p pub.pubBytes pub.tag n c T).map fun ctx =>
    (QueryNextLaw.own p c, (missing p T ctx).map fun b => (b, none), output p pub T n ctx)

/-- The unified-dispatcher form (`List State` own output), as R1's components. -/
def component (p : Params M Cv L) (pub : UnifiedSampler.Public L) (n : Nat) :
    Decoder.UDec M Cv L :=
  DecoderStateList.lift (decode p pub n)

theorem decode_of_parse (p : Params M Cv L) (pub : UnifiedSampler.Public L) (n : Nat)
    (c : Addr L) (T : Table (Addr L) State) (ctx : Context.Context M L)
    (h : Context.parse p pub.pubBytes pub.tag n c T = some ctx) :
    decode p pub n c T =
      some (QueryNextLaw.own p c, (missing p T ctx).map fun b => (b, none), output p pub T n ctx) := by
  simp only [decode, h, Option.map_some]

theorem decode_sound (p : Params M Cv L) (pub : UnifiedSampler.Public L) (n : Nat)
    (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub n c T = some (own, pend, g)) :
    ∃ ctx, Context.parse p pub.pubBytes pub.tag n c T = some ctx ∧
      (QueryNextLaw.own p c, (missing p T ctx).map fun b => (b, none), output p pub T n ctx) =
        (own, pend, g) := by
  cases hp : Context.parse p pub.pubBytes pub.tag n c T with
  | none => simp [decode, hp] at hd
  | some ctx =>
      refine ⟨ctx, rfl, ?_⟩
      rw [decode_of_parse p pub n c T ctx hp] at hd
      exact Option.some.inj hd

/-! ## Round count of the output prefix -/

theorem prefixOf_length (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (T : Table (Addr L) State) (n : Nat) (hlo : 33 ≤ n) (c : Addr L)
    (ctx : Context.Context M L)
    (hp : Context.parse p pub.pubBytes pub.tag n c T = some ctx) (as : List State) :
    (prefixOf p pub T ctx as).rounds.length = n := by
  obtain ⟨_, hj, hl, ht⟩ := Context.parse_sound p pub.pubBytes pub.tag n c T ctx hp
  have h32 := JointTranscriptView.parsed_prefix_length p pub 27 4 ctx.rhoAbsorb T ctx.joint
    hj hl (as.take (jointMissing p T ctx).length)
  simp only [prefixOf, List.length_append, later, List.length_map, laterRows_length,
    List.length_zip, messages, squeezes, frames, nexts, List.length_cons]
  rw [h32, ht]
  omega

/-! ## Law and bound -/

theorem messageValid_final (n : Nat) (hlo : 33 ≤ n) (m : M) :
    UnifiedSampler.messageValid n (.payload m) := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  trivial

theorem output_append (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (T : Table (Addr L) State) (n : Nat) (ctx : Context.Context M L)
    (as bs : List State) (x : State) (hlen : as.length = (missing p T ctx).length) :
    output p pub T n ctx x (as ++ bs) =
      (prefixOf p pub T ctx as, .payload ctx.message,
        liftChallenge (p.σ n (bs.headD default), x)) := by
  dsimp only [output]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
    List.nil_append]

/-- Copy of `JointUnifiedLaw.background_sampler_law` for rows 33 to 39. -/
theorem background_sampler_law (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (T : Table (Addr L) State) (n : Nat) (hlo : 33 ≤ n)
    (ctx : Context.Context M L) (c : Addr L)
    (obs : JointTranscriptView.Output M Cv L → ℚ) :
    blaw (output p pub T n ctx) obs (QueryNextLaw.own p c)
        ((missing p T ctx).map fun b => (b, none)) =
      pmean (fun as => independentMean
        (UnifiedSampler.samp p hD n (prefixOf p pub T ctx as) (.payload ctx.message)).toProgram
        (fun w => obs (prefixOf p pub T ctx as, .payload ctx.message, w.2)))
        ((missing p T ctx).map fun b => (b, none)) := by
  have hsplit := blaw_split (output p pub T n ctx) obs (QueryNextLaw.own p c)
    ((missing p T ctx).map fun b => (b, none)) []
  rw [List.append_nil] at hsplit
  rw [hsplit]
  apply BackgroundMean.pmean_congr_length
  intro as has
  have hlen : as.length = (missing p T ctx).length := by
    simpa only [List.length_map] using has
  have hfun : (fun x bs => output p pub T n ctx x (as ++ bs)) =
      fun x bs => (fun ch : Chal Cv => (prefixOf p pub T ctx as, (.payload ctx.message : Message M),
        liftChallenge ch)) (p.σ n (bs.headD default), x) := by
    funext x bs
    exact output_append p pub T n ctx as bs x hlen
  rw [hfun, QueryNextLaw.own_law p c n (fun ch : Chal Cv => (prefixOf p pub T ctx as,
    (.payload ctx.message : Message M), liftChallenge ch)) obs]
  rw [UnifiedSampler.unified_law p hD n (prefixOf p pub T ctx as) (.payload ctx.message)
    (fun ch => obs (prefixOf p pub T ctx as, .payload ctx.message, ch)) (by omega)
    (messageValid_final n hlo ctx.message)]

/-- Copy of `JointUnifiedBound.decoded_bound` for rows 33 to 39: a fixed-prefix
bound on row n's sampler for every completed prefix bounds the background
law of the decoded start. -/
theorem decoded_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (n : Nat) (hlo : 33 ≤ n)
    (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub n c T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ ctx,
      Context.parse p pub.pubBytes pub.tag n c T = some ctx →
      ∀ as, as.length = (missing p T ctx).length →
        independentMean
          (UnifiedSampler.samp p hD n (prefixOf p pub T ctx as) (.payload ctx.message)).toProgram
          (fun w => obs (prefixOf p pub T ctx as, .payload ctx.message, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  obtain ⟨ctx, hparse, hshape⟩ := decode_sound p pub n c T own pend g hd
  cases hshape
  rw [background_sampler_law p hD pub T n hlo ctx c obs]
  apply pmean_le
  intro as has
  have hlenAs : as.length = (missing p T ctx).length := by
    simpa only [List.length_map] using has
  exact hfixed ctx hparse as hlenAs

/-- The same bound for the unified-dispatcher form. -/
theorem component_bound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (n : Nat) (hlo : 33 ≤ n)
    (c : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State)) (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : component p pub n c T = some (own, pend, g))
    (obs : JointTranscriptView.Output M Cv L → ℚ) (B : ℚ)
    (hfixed : ∀ ctx,
      Context.parse p pub.pubBytes pub.tag n c T = some ctx →
      ∀ as, as.length = (missing p T ctx).length →
        independentMean
          (UnifiedSampler.samp p hD n (prefixOf p pub T ctx as) (.payload ctx.message)).toProgram
          (fun w => obs (prefixOf p pub T ctx as, .payload ctx.message, w.2)) ≤ B) :
    blaw g obs own pend ≤ B := by
  obtain ⟨own₀, pend₀, g₀, hd₀, he⟩ := DecoderStateList.lift_sound (decode p pub n) c T own pend g hd
  simp only [Prod.mk.injEq] at he
  obtain ⟨rfl, rfl, rfl⟩ := he
  rw [DecoderStateList.lifted_law]
  exact decoded_bound p hD pub n hlo c T own₀ pend₀ g₀ hd₀ obs B hfixed

/-! ## Canonical addresses -/

theorem missing_canonical (p : Params M Cv L) (T : Table (Addr L) State)
    (ctx : Context.Context M L) (a : Addr L) (ha : a ∈ missing p T ctx) : Canonical a := by
  rcases List.mem_append.mp ha with hj | hn
  · exact joint_missing p T ctx.joint.records ctx.joint.endpoint a hj
  · obtain ⟨f, _, he⟩ := List.mem_map.mp (List.mem_filter.mp (List.mem_dedup.mp hn)).1
    rw [← he]
    exact canonical_ofBytes _ _

/-- Analogue of `UnifiedDecoderCanonical.decode_good` for this component. -/
theorem decode_good (p : Params M Cv L) (pub : UnifiedSampler.Public L) (n : Nat)
    (c : Addr L) (hc : Canonical c) (T : Table (Addr L) State)
    (own : BS (Addr L) State State) (pend : List (Addr L × Option State))
    (g : State → List State → JointTranscriptView.Output M Cv L)
    (hd : decode p pub n c T = some (own, pend, g)) : Good own pend := by
  obtain ⟨ctx, _, he⟩ := decode_sound p pub n c T own pend g hd
  cases he
  exact ⟨plain p c hc, pend_of_canonical _ (missing_canonical p T ctx)⟩

theorem component_good (p : Params M Cv L) (pub : UnifiedSampler.Public L) (n : Nat)
    (c : Addr L) (hc : Canonical c) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State)) (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hd : component p pub n c T = some (own, pend, g)) : Good own pend :=
  lifted_good _ c T own pend g hd (fun s ps out hs => decode_good p pub n c hc T s ps out hs)

#print axioms laterRows_length
#print axioms decode_of_parse
#print axioms decode_sound
#print axioms prefixOf_length
#print axioms messageValid_final
#print axioms output_append
#print axioms background_sampler_law
#print axioms decoded_bound
#print axioms component_bound
#print axioms missing_canonical
#print axioms decode_good
#print axioms component_good

end AspisRows40.Final
end
