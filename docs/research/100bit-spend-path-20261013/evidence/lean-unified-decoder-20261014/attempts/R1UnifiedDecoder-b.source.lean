import R1DecoderStateList
import R1UnifiedInitialDecoder
import R1UnifiedSemanticDecoder
import R1UnifiedReseedDecoder
import R1UnifiedOpeningDecoder
import R1UnifiedQueryDecoder
import R1JointUnifiedDecoder
import R1UnifiedLabels
import R1PublicInitAbsorbSeparation

/-! Row-indexed composition of the already defined typed decoders.
This module only dispatches deterministic decoder components. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.UnifiedDecoder

open FS FS2 FS2.Duplex R0C.V3
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

def component (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (n : Nat) :
    Dec (UnifiedSampler.Public L) (Message M) (Challenge Cv)
      (Addr L) State (List State) :=
  if n = 0 then DecoderStateList.lift (UnifiedInitialDecoder.decode p hD pub)
  else if n < 26 then DecoderStateList.lift (UnifiedSemanticDecoder.decode p pub)
  else if n = 26 then DecoderStateList.lift (UnifiedReseedDecoder.decode p pub)
  else if n < 31 then DecoderStateList.lift (UnifiedOpeningDecoder.decode p pub)
  else if n = 31 then UnifiedQueryDecoder.decode p pub
  else if n = 32 then DecoderStateList.lift (JointUnifiedDecoder.decode p pub 27 4)
  else fun _ _ => none

def decode (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) :
    Dec (UnifiedSampler.Public L) (Message M) (Challenge Cv)
      (Addr L) State (List State) :=
  fun a T =>
    if (PublicInitParse.parse pub.pubBytes a).isSome then
      component p hD pub 0 a T
    else
      (parseAbsorb a).bind fun (_, label, _) =>
        component p hD pub (UnifiedLabels.row label) a T

theorem component_initial (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) :
    component p hD pub 0 = DecoderStateList.lift (UnifiedInitialDecoder.decode p hD pub) := by
  simp [component]

theorem component_semantic (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (n : Nat) (h0 : 0 < n) (h26 : n < 26) :
    component p hD pub n = DecoderStateList.lift (UnifiedSemanticDecoder.decode p pub) := by
  unfold component
  rw [if_neg (by omega : n ≠ 0), if_pos h26]

theorem component_reseed (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) :
    component p hD pub 26 = DecoderStateList.lift (UnifiedReseedDecoder.decode p pub) := by
  simp [component]

theorem component_opening (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (n : Nat) (hlo : 27 ≤ n) (hhi : n < 31) :
    component p hD pub n = DecoderStateList.lift (UnifiedOpeningDecoder.decode p pub) := by
  unfold component
  rw [if_neg (by omega : n ≠ 0), if_neg (by omega : ¬ n < 26),
    if_neg (by omega : n ≠ 26), if_pos hhi]

theorem component_query (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) :
    component p hD pub 31 = UnifiedQueryDecoder.decode p pub := by
  simp [component]

theorem component_rho (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) :
    component p hD pub 32 =
      DecoderStateList.lift (JointUnifiedDecoder.decode p pub 27 4) := by
  simp [component]

theorem component_none (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (n : Nat) (hn : 33 ≤ n) :
    component p hD pub n = fun _ _ => none := by
  unfold component
  have hn0 : n ≠ 0 := by omega
  have hn26 : ¬ n < 26 := by omega
  have hn26eq : n ≠ 26 := by omega
  have hn31 : ¬ n < 31 := by omega
  have hn31eq : n ≠ 31 := by omega
  have hn32eq : n ≠ 32 := by omega
  simp [hn0, hn26, hn26eq, hn31, hn31eq, hn32eq]

theorem decode_of_init_parse (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (c1 : State) (hparse : PublicInitParse.parse pub.pubBytes a = some c1) :
    decode p hD pub a T = component p hD pub 0 a T := by
  simp [decode, hparse]

theorem decode_of_absorb (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (T : Table (Addr L) State)
    (s : State) (n : Nat) (data : Bytes) (hdata : data.length ≤ p.D)
    (hn : n < 33) (hl : p.lbl n = UnifiedLabels.label n) :
    decode p hD pub (absorbA p s (p.lbl n) data hdata) T =
      component p hD pub n (absorbA p s (p.lbl n) data hdata) T := by
  have hinit := PublicInitAbsorbSeparation.parse_init_absorb_none p pub.pubBytes
    s (p.lbl n) data hdata
  have hrow : UnifiedLabels.row (p.lbl n) = n := by
    rw [hl]
    exact UnifiedLabels.row_label n hn
  simp [decode, hinit, parseAbsorb_absorbA, hrow]

theorem decode_sound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hdecode : decode p hD pub a T = some (own, pend, g)) :
    ∃ n, n < 33 ∧ component p hD pub n a T = some (own, pend, g) := by
  unfold decode at hdecode
  by_cases hinit : (PublicInitParse.parse pub.pubBytes a).isSome
  · simp only [if_pos hinit] at hdecode
    refine ⟨0, by omega, ?_⟩
    simpa [component] using hdecode
  · simp only [if_neg hinit] at hdecode
    cases hp : parseAbsorb a with
    | none => simp [hp] at hdecode
    | some parsed =>
        rcases parsed with ⟨endpoint, label, data⟩
        simp only [hp, Option.bind_some] at hdecode
        let n := UnifiedLabels.row label
        have hcomponent : component p hD pub n a T = some (own, pend, g) := by
          simpa [n] using hdecode
        have hn : n < 33 := by
          by_contra hnot
          have hge : 33 ≤ n := by omega
          have hnone := component_none p hD pub n hge
          rw [hnone] at hcomponent
          simp at hcomponent
        exact ⟨n, hn, hcomponent⟩

#print axioms component_initial
#print axioms component_semantic
#print axioms component_reseed
#print axioms component_opening
#print axioms component_query
#print axioms component_rho
#print axioms component_none
#print axioms decode_of_init_parse
#print axioms decode_of_absorb
#print axioms decode_sound

end AspisR1.UnifiedDecoder
end
