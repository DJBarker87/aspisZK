import R1SelectedChallengeMap
import R1UnifiedSampler
import R1SemanticPublicCodecComplete

/-! A bounded raw-message parameterization for the selected 33-row model.
The message codec only enforces the chosen 3717-byte bound. This file does
not establish row-specific message validity, Rust refinement, a complete
protocol decision, or a security theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.SelectedTranscriptParams

open AspisV8R19.DuplexFrames
open AspisV8R19.SourceDuplexStep
open AspisR1.TranscriptView

def L : Nat := 131072
def D : Nat := 3717

abbrev Message := { bs : Bytes // bs.length ≤ D }

def enc (m : Message) : Bytes := m.1

def dec (bs : Bytes) : Option Message :=
  if h : bs.length ≤ D then some ⟨bs, h⟩ else none

theorem dec_enc (m : Message) : dec (enc m) = some m := by
  simp [dec, enc, m.2]

def label (i : Nat) : Byte := ⟨(160 + i) % 256, Nat.mod_lt _ (by decide)⟩

theorem label_val (i : Nat) (hi : i < 33) : (label i).val = 160 + i := by
  change (160 + i) % 256 = 160 + i
  exact Nat.mod_eq_of_lt (by omega)

theorem label_zero : label 0 = (160 : Byte) := by
  apply Fin.ext
  simp [label]

def params : FS2.Duplex.Params Message AspisWideTower.WideExact L :=
  { D := D
    hL := by norm_num [D, L]
    enc := enc
    encLen := fun m => m.2
    dec := dec
    decEnc := dec_enc
    lbl := label
    σ := SelectedChallengeMap.sigma
    iv := 0
    rounds := 33 }

theorem params_sigma (i : Nat) (s : State) :
    params.σ i s = SelectedChallengeMap.sigma i s := rfl

theorem params_label_zero : params.lbl 0 = (160 : Byte) := label_zero

def publicStatement (bytes : List SemanticPublicWire.Byte)
    (pub : R0P.Public SemanticPublicWire.M31)
    (hparse : SemanticPublicWire.parsePublic bytes = some pub) :
    UnifiedSampler.Public L :=
  ⟨bytes, by
      have hfit := SemanticPublicCodecComplete.parsed_init_fits bytes pub hparse
      dsimp only [L]
      omega,
    (2 : Byte)⟩

theorem publicStatement_bytes (bytes : List SemanticPublicWire.Byte)
    (pub : R0P.Public SemanticPublicWire.M31)
    (hparse : SemanticPublicWire.parsePublic bytes = some pub) :
    (publicStatement bytes pub hparse).pubBytes = bytes := rfl

theorem publicStatement_tag (bytes : List SemanticPublicWire.Byte)
    (pub : R0P.Public SemanticPublicWire.M31)
    (hparse : SemanticPublicWire.parsePublic bytes = some pub) :
    (publicStatement bytes pub hparse).tag = (2 : Byte) := rfl

theorem publicStatement_initFits (bytes : List SemanticPublicWire.Byte)
    (pub : R0P.Public SemanticPublicWire.M31)
    (hparse : SemanticPublicWire.parsePublic bytes = some pub) :
    75 + (publicStatement bytes pub hparse).pubBytes.length ≤ L :=
  (publicStatement bytes pub hparse).initFits

#print axioms dec_enc
#print axioms label_val
#print axioms label_zero
#print axioms params_sigma
#print axioms params_label_zero
#print axioms publicStatement_bytes
#print axioms publicStatement_tag
#print axioms publicStatement_initFits

end AspisR1.SelectedTranscriptParams
end
