import R1PublicInitFrame
import R1OpeningReseedFrame
import R1SelectedTranscriptParams

/-! Executable raw byte framing. No protocol sampler, challenge decoder or
specification-level extractor is evaluated. Compatibility is proved against
the retained semantic frame definitions. -/
set_option autoImplicit false
namespace AspisR1.RawTranscriptFrameBytes

open FS2.Duplex
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def semanticDomain : Bytes :=
  [85, 78, 80, 82, 79, 86, 69, 68, 58, 82, 49, 58, 80, 82, 73,
   86, 65, 84, 69, 45, 83, 65, 76, 84, 69, 68, 58, 83, 69, 77,
   65, 78, 84, 73, 67, 58, 80, 51]

def openingDomain : Bytes :=
  [85, 78, 80, 82, 79, 86, 69, 68, 58, 82, 49, 58, 80, 82, 73,
   86, 65, 84, 69, 45, 83, 65, 76, 84, 69, 68, 58, 80, 51]

def lengthBytes (n : Nat) : Bytes :=
  List.ofFn fun j : Fin 4 =>
    (⟨(n / 256^j.val) % 256, Nat.mod_lt _ (by decide)⟩ : Byte)

def label (i : Nat) : Byte :=
  ⟨(160 + i) % 256, Nat.mod_lt _ (by decide)⟩

def publicInit (pub : Bytes) (root : State) : Bytes :=
  (semanticDomain ++ [0] ++ lengthBytes pub.length ++ pub) ++ bytes root

def absorb (state : State) (row : Nat) (payload : Bytes) : Bytes :=
  bytes state ++ [0, label row] ++ payload

def rowZero (state : State) : Bytes :=
  bytes state ++ [0, 160] ++ [0, 0, 0, 0, 0]

def advance (state : State) : Bytes := bytes state ++ [2]

def reseed (tag : Byte) (state : State) : Bytes :=
  openingDomain ++ [tag] ++ bytes state

theorem publicInit_eq {L : Nat} (pub : Bytes)
    (hfit : 75 + pub.length ≤ L) (root : State) :
    publicInit pub root = (PublicInitFrame.addr pub hfit root).toBytes := by
  rw [PublicInitFrame.addr_bytes]
  simp only [publicInit, semanticDomain, lengthBytes, PublicInitFrame.domain,
    PublicInitFrame.lengthBytes, List.append_assoc]

theorem absorb_eq (state : State) (row : Nat)
    (payload : SelectedTranscriptParams.Message) :
    absorb state row payload.val =
      (absorbA SelectedTranscriptParams.params state
        (SelectedTranscriptParams.params.lbl row)
        (SelectedTranscriptParams.params.enc payload)
        (SelectedTranscriptParams.params.encLen payload)).toBytes := by
  rw [absorbA, Addr.toBytes_ofBytes]
  rfl

theorem rowZero_eq {M C : Type} {L : Nat} (p : Params M C L)
    (hD : 5 ≤ p.D) (state : State) :
    rowZero state = (PublicInitFrame.row0 p hD state).toBytes := by
  rw [PublicInitFrame.row0_bytes]
  rfl

theorem advance_eq {M C : Type} {L : Nat} (p : Params M C L) (state : State) :
    advance state = (advanceA p state).toBytes := by
  rw [advanceA, Addr.toBytes_ofBytes]
  rfl

theorem reseed_eq {L : Nat} (tag : Byte) (hfit : 62 ≤ L) (state : State) :
    reseed tag state = (OpeningReseedFrame.addr tag hfit state).toBytes := by
  rw [OpeningReseedFrame.addr_bytes]
  rfl

#print axioms publicInit
#print axioms absorb
#print axioms advance
#print axioms reseed
#print axioms publicInit_eq
#print axioms absorb_eq
#print axioms rowZero_eq
#print axioms advance_eq
#print axioms reseed_eq
end AspisR1.RawTranscriptFrameBytes
