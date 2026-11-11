import R1UnifiedDecoder
import AspisRows40Labels

/-! Aspis one-transaction verifier: the unified decoder dispatch for 40 rows.

R1's `UnifiedDecoder.component` sends rows 33 and above to `none`
(`component_none`, `33 ≤ n`), and `decode_of_absorb` / `decode_sound` carry
`n < 33`. This file defines a PARALLEL dispatcher: rows 0 to 32 go to R1's
components unchanged (`component_r1`), rows 33 to 39 go to a final-sumcheck
component `fin n` supplied as a parameter, rows 40 and above to `none`. The
facts proved here hold for every `fin`; they are what a start count needs:
the dispatch of an absorb frame is its label's row (`decode_of_absorb`),
nothing decodes outside rows 0 to 39 (`decode_sound`), squeeze and advance
frames never decode (`squeeze_none`, `advance_none`), and R1's decoder rejects
every frame whose label is a new row (`r1_none_of_final`), so on R1's frames
the two decoders agree (`decode_eq_r1`).

A concrete `fin` (the completing decoder of rows 33 to 39, with its law) is not
constructed here; see AspisRows40Context for its context parser. -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.Decoder

open FS FS2 FS2.Duplex R0C.V3
open AspisR1
open AspisV8PairedCommitment
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

variable {M Cv : Type} {L : Nat}

/-- The decoder type of R1's unified dispatcher. -/
abbrev UDec (M Cv : Type) (L : Nat) :=
  Dec (UnifiedSampler.Public L) (Message M) (Challenge Cv) (Addr L) State (List State)

def component (p : Params M Cv L) (hD : 5 ≤ p.D) (pub : UnifiedSampler.Public L)
    (fin : Nat → UDec M Cv L) (n : Nat) : UDec M Cv L :=
  if n < 33 then UnifiedDecoder.component p hD pub n
  else if n < 40 then fin n
  else fun _ _ => none

def decode (p : Params M Cv L) (hD : 5 ≤ p.D) (pub : UnifiedSampler.Public L)
    (fin : Nat → UDec M Cv L) : UDec M Cv L :=
  fun a T =>
    if (PublicInitParse.parse pub.pubBytes a).isSome then
      component p hD pub fin 0 a T
    else
      (parseAbsorb a).bind fun (_, label, _) =>
        component p hD pub fin (UnifiedLabels.row label) a T

/-- Row index of an address as the dispatch sees it (`none` if neither an
initialization frame nor an absorb frame). -/
def rowOf (pub : UnifiedSampler.Public L) (a : Addr L) : Option Nat :=
  if (PublicInitParse.parse pub.pubBytes a).isSome then some 0
  else (parseAbsorb a).map fun (_, label, _) => UnifiedLabels.row label

theorem component_r1 (p : Params M Cv L) (hD : 5 ≤ p.D) (pub : UnifiedSampler.Public L)
    (fin : Nat → UDec M Cv L) (n : Nat) (hn : n < 33) :
    component p hD pub fin n = UnifiedDecoder.component p hD pub n := by
  simp [component, hn]

theorem component_final (p : Params M Cv L) (hD : 5 ≤ p.D) (pub : UnifiedSampler.Public L)
    (fin : Nat → UDec M Cv L) (n : Nat) (hlo : 33 ≤ n) (hhi : n < 40) :
    component p hD pub fin n = fin n := by
  unfold component
  rw [if_neg (by omega), if_pos hhi]

theorem component_none (p : Params M Cv L) (hD : 5 ≤ p.D) (pub : UnifiedSampler.Public L)
    (fin : Nat → UDec M Cv L) (n : Nat) (hn : 40 ≤ n) :
    component p hD pub fin n = fun _ _ => none := by
  unfold component
  rw [if_neg (by omega), if_neg (by omega)]

theorem decode_of_init_parse (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (fin : Nat → UDec M Cv L)
    (a : Addr L) (T : Table (Addr L) State)
    (c1 : State) (hparse : PublicInitParse.parse pub.pubBytes a = some c1) :
    decode p hD pub fin a T = component p hD pub fin 0 a T := by
  simp [decode, hparse]

theorem decode_of_absorb (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (fin : Nat → UDec M Cv L) (T : Table (Addr L) State)
    (s : State) (n : Nat) (data : Bytes) (hdata : data.length ≤ p.D)
    (hn : n < 40) (hl : p.lbl n = UnifiedLabels.label n) :
    decode p hD pub fin (absorbA p s (p.lbl n) data hdata) T =
      component p hD pub fin n (absorbA p s (p.lbl n) data hdata) T := by
  have hinit := PublicInitAbsorbSeparation.parse_init_absorb_none p pub.pubBytes
    s (p.lbl n) data hdata
  have hrow : UnifiedLabels.row (p.lbl n) = n := by
    rw [hl]
    exact Labels.row_label n hn
  simp [decode, hinit, parseAbsorb_absorbA, hrow]

theorem rowOf_absorb (p : Params M Cv L) (pub : UnifiedSampler.Public L)
    (s : State) (n : Nat) (data : Bytes) (hdata : data.length ≤ p.D)
    (hn : n < 40) (hl : p.lbl n = UnifiedLabels.label n) :
    rowOf pub (absorbA p s (p.lbl n) data hdata) = some n := by
  have hinit := PublicInitAbsorbSeparation.parse_init_absorb_none p pub.pubBytes
    s (p.lbl n) data hdata
  have hrow : UnifiedLabels.row (p.lbl n) = n := by
    rw [hl]
    exact Labels.row_label n hn
  simp [rowOf, hinit, parseAbsorb_absorbA, hrow]

/-- The decoder decodes only through its dispatch row, which is below 40. -/
theorem decode_sound (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (fin : Nat → UDec M Cv L)
    (a : Addr L) (T : Table (Addr L) State)
    (own : BS (Addr L) State (List State))
    (pend : List (Addr L × Option State))
    (g : List State → List State → JointTranscriptView.Output M Cv L)
    (hdecode : decode p hD pub fin a T = some (own, pend, g)) :
    ∃ n, n < 40 ∧ rowOf pub a = some n ∧ component p hD pub fin n a T = some (own, pend, g) := by
  unfold decode at hdecode
  by_cases hinit : (PublicInitParse.parse pub.pubBytes a).isSome
  · simp only [if_pos hinit] at hdecode
    exact ⟨0, by omega, by simp [rowOf, hinit], hdecode⟩
  · simp only [if_neg hinit] at hdecode
    cases hp : parseAbsorb a with
    | none => simp [hp] at hdecode
    | some parsed =>
        rcases parsed with ⟨endpoint, label, data⟩
        simp only [hp, Option.bind_some] at hdecode
        let n := UnifiedLabels.row label
        have hcomponent : component p hD pub fin n a T = some (own, pend, g) := by
          simpa [n] using hdecode
        have hn : n < 40 := by
          by_contra hnot
          have hnone := component_none p hD pub fin n (by omega)
          rw [hnone] at hcomponent
          simp at hcomponent
        exact ⟨n, hn, by simp [rowOf, hinit, hp, n], hcomponent⟩

/-! ## Frames that never decode -/

theorem init_none_of_short (pubBytes : Bytes) (a : Addr L) (h : a.toBytes.length < 75) :
    PublicInitParse.parse pubBytes a = none := by
  cases hp : PublicInitParse.parse pubBytes a with
  | none => rfl
  | some root =>
      have hb := (PublicInitParse.parse_sound pubBytes a root hp).2
      have hl := congrArg List.length hb
      simp only [List.length_append, List.length_cons, List.length_nil, bytes_length] at hl
      norm_num [PublicInitFrame.domain, PublicInitFrame.lengthBytes] at hl
      omega

theorem decode_none_of_short (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (fin : Nat → UDec M Cv L)
    (a : Addr L) (T : Table (Addr L) State)
    (hshort : a.toBytes.length < 34) : decode p hD pub fin a T = none := by
  have hi := init_none_of_short pub.pubBytes a (by omega)
  have ha : parseAbsorb a = none := by
    unfold parseAbsorb
    rw [if_neg (by omega)]
  simp [decode, hi, ha]

theorem squeeze_none (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (fin : Nat → UDec M Cv L)
    (s : State) (T : Table (Addr L) State) :
    decode p hD pub fin (squeezeA p s) T = none := by
  apply decode_none_of_short
  simp [squeezeA, Addr.toBytes_ofBytes, squeeze, bytes_length]

theorem advance_none (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (fin : Nat → UDec M Cv L)
    (s : State) (T : Table (Addr L) State) :
    decode p hD pub fin (advanceA p s) T = none := by
  apply decode_none_of_short
  simp [advanceA, Addr.toBytes_ofBytes, advance, bytes_length]

/-! ## Agreement with R1 -/

/-- R1's decoder rejects every absorb frame whose label is row 33 or later. -/
theorem r1_none_of_final (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (a : Addr L) (T : Table (Addr L) State)
    (s : State) (label : Byte) (data : Bytes)
    (hp : parseAbsorb a = some (s, label, data)) (hrow : 33 ≤ UnifiedLabels.row label) :
    UnifiedDecoder.decode p hD pub a T = none := by
  have hinit : PublicInitParse.parse pub.pubBytes a = none := by
    cases hi : PublicInitParse.parse pub.pubBytes a with
    | none => rfl
    | some c1 =>
        have := PublicInitAbsorbSeparation.parseAbsorb_none_of_init pub.pubBytes a c1 hi
        rw [hp] at this
        cases this
  simp [UnifiedDecoder.decode, hinit, hp, UnifiedDecoder.component_none p hD pub _ hrow]

/-- Where the dispatch row is below 33 (or the address is no frame), the 40-row
decoder IS R1's decoder. -/
theorem decode_eq_r1 (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (fin : Nat → UDec M Cv L)
    (a : Addr L) (T : Table (Addr L) State)
    (hrow : ∀ n, rowOf pub a = some n → n < 33) :
    decode p hD pub fin a T = UnifiedDecoder.decode p hD pub a T := by
  unfold decode UnifiedDecoder.decode
  by_cases hinit : (PublicInitParse.parse pub.pubBytes a).isSome
  · simp only [if_pos hinit]
    exact congrFun (congrFun (component_r1 p hD pub fin 0 (by omega)) a) T
  · simp only [if_neg hinit]
    cases hp : parseAbsorb a with
    | none => simp only [Option.bind_none]
    | some parsed =>
        rcases parsed with ⟨endpoint, label, data⟩
        simp only [Option.bind_some]
        have hn := hrow (UnifiedLabels.row label) (by simp [rowOf, hinit, hp])
        exact congrFun (congrFun (component_r1 p hD pub fin _ hn) a) T

/-- On a frame of a new row, the 40-row decoder is the final component and R1's
decoder is `none`. -/
theorem decode_final (p : Params M Cv L) (hD : 5 ≤ p.D)
    (pub : UnifiedSampler.Public L) (fin : Nat → UDec M Cv L)
    (a : Addr L) (T : Table (Addr L) State)
    (s : State) (label : Byte) (data : Bytes)
    (hp : parseAbsorb a = some (s, label, data))
    (hlo : 33 ≤ UnifiedLabels.row label) (hhi : UnifiedLabels.row label < 40) :
    decode p hD pub fin a T = fin (UnifiedLabels.row label) a T ∧
      UnifiedDecoder.decode p hD pub a T = none := by
  refine ⟨?_, r1_none_of_final p hD pub a T s label data hp hlo⟩
  have hinit : PublicInitParse.parse pub.pubBytes a = none := by
    cases hi : PublicInitParse.parse pub.pubBytes a with
    | none => rfl
    | some c1 =>
        have := PublicInitAbsorbSeparation.parseAbsorb_none_of_init pub.pubBytes a c1 hi
        rw [hp] at this
        cases this
  unfold decode
  rw [if_neg (by simp [hinit]), hp, Option.bind_some]
  exact congrFun (congrFun (component_final p hD pub fin _ hlo hhi) a) T

#print axioms component_r1
#print axioms component_final
#print axioms component_none
#print axioms decode_of_init_parse
#print axioms decode_of_absorb
#print axioms rowOf_absorb
#print axioms decode_sound
#print axioms init_none_of_short
#print axioms decode_none_of_short
#print axioms squeeze_none
#print axioms advance_none
#print axioms r1_none_of_final
#print axioms decode_eq_r1
#print axioms decode_final

end AspisRows40.Decoder
end
