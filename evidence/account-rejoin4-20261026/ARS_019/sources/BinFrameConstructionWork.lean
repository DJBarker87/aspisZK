import PublicPrimitiveDecoderWork
import BinFrameSizeBound

/-! Frame/address construction with cumulative list-copy work. Serialization
uses a fixed tariff: state is eight fixed-width words; length encodings are
four bytes. The callers below bound lengths by the protocol carrier. -/
set_option autoImplicit false
namespace AspisR1.BinFrameConstructionWork
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RawTranscriptFrameBytes
abbrev W := List Byte × Nat

def literal (xs : List Byte) : W := (xs, xs.length+1)
def stateBytes (s : State) : W := (bytes s, 512)
def join (x y : W) : W :=
  let r := BinLeafListWork.append x.1 y.1
  (r.1, x.2 + y.2 + r.2 + 2)

theorem join_value (x y : W) : (join x y).1 = x.1 ++ y.1 :=
  BinLeafListWork.append_value _ _

theorem join_work (x y : W) : (join x y).2 = x.2+y.2+2*x.1.length+3 := by
  simp only [join, BinLeafListWork.append_work]; omega

def publicInit (pub : Bytes) (root : State) : W :=
  let len := PublicPrimitiveDecoderWork.length pub
  let header := join (literal semanticDomain) (literal [0])
  let header := join header (lengthBytes len.1, len.2 + 128)
  join (join header (pub, 0)) (stateBytes root)

theorem publicInit_value (pub : Bytes) (root : State) :
    (publicInit pub root).1 = RawTranscriptFrameBytes.publicInit pub root := by
  simp only [publicInit, join_value, literal, stateBytes,
    PublicPrimitiveDecoderWork.length_value, RawTranscriptFrameBytes.publicInit,
    List.append_assoc]

theorem publicInit_work (pub : Bytes) (root : State) :
    (publicInit pub root).2 ≤ 3*pub.length+2048 := by
  simp only [publicInit, join_work, join_value, literal, stateBytes,
    PublicPrimitiveDecoderWork.length_work, List.length_append, List.length_cons,
    List.length_nil, semanticDomain, lengthBytes, List.length_ofFn, bytes_length]
  omega

def absorb (s : State) (row : Nat) (p : Bytes) : W :=
  join (join (stateBytes s) ([0, label row], 64)) (p, 0)

theorem absorb_value (s : State) (row : Nat) (p : Bytes) :
    (absorb s row p).1 = RawTranscriptFrameBytes.absorb s row p := by
  simp only [absorb, join_value, stateBytes, RawTranscriptFrameBytes.absorb]

theorem absorb_work (s : State) (row : Nat) (p : Bytes) :
    (absorb s row p).2 ≤ 1024 := by
  simp only [absorb, join_work, join_value, stateBytes, List.length_append,
    List.length_cons, List.length_nil, bytes_length]
  omega

def rowZero (s : State) : W :=
  join (join (stateBytes s) (literal [0,160])) (literal [0,0,0,0,0])
def advance (s : State) : W := join (stateBytes s) (literal [2])
def reseed (tag : Byte) (s : State) : W :=
  join (join (literal openingDomain) (literal [tag])) (stateBytes s)

theorem rowZero_value (s : State) : (rowZero s).1 = RawTranscriptFrameBytes.rowZero s := by
  simp only [rowZero, join_value, literal, stateBytes, RawTranscriptFrameBytes.rowZero]
theorem advance_value (s : State) : (advance s).1 = RawTranscriptFrameBytes.advance s := by
  simp only [advance, join_value, literal, stateBytes, RawTranscriptFrameBytes.advance]
theorem reseed_value (tag : Byte) (s : State) : (reseed tag s).1 = RawTranscriptFrameBytes.reseed tag s := by
  simp only [reseed, join_value, literal, stateBytes, RawTranscriptFrameBytes.reseed]

theorem rowZero_work (s : State) : (rowZero s).2 ≤ 1024 := by
  simp only [rowZero, join_work, join_value, literal, stateBytes, bytes_length,
    List.length_append, List.length_cons, List.length_nil]
  omega
theorem advance_work (s : State) : (advance s).2 ≤ 1024 := by
  simp only [advance, join_work, literal, stateBytes, bytes_length,
    List.length_cons, List.length_nil]
  omega
theorem reseed_work (tag : Byte) (s : State) : (reseed tag s).2 ≤ 1024 := by
  simp only [reseed, join_work, join_value, literal, stateBytes, bytes_length,
    openingDomain, List.length_append, List.length_cons, List.length_nil]
  omega

#print axioms join_value
#print axioms join_work
#print axioms publicInit_value
#print axioms publicInit_work
#print axioms absorb_value
#print axioms absorb_work
#print axioms rowZero_value
#print axioms advance_value
#print axioms reseed_value
#print axioms rowZero_work
#print axioms advance_work
#print axioms reseed_work
end AspisR1.BinFrameConstructionWork
