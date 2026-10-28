import R1Z.LayoutTagR1PBin

/-! Concrete logical R1/S2 byte-shape carrier. Fixed-size vectors describe
payload slices, without assuming field canonicality. Compact stored fields
are expanded to these logical widths before transcript hashing.
This is the wire grammar; identification with a Rust execution remains R-wire. -/
set_option autoImplicit false
namespace R1Z.WireLengthsR1PBin
open R0Z.FsStatement R1Z.LensR1 R1Z.TranscriptR1 R1Z.LayoutR1PBin

def semanticSize (i : Fin 27) : Nat :=
  if i.val = 2 ∨ i.val = 14 then 32
  else if 15 ≤ i.val ∧ i.val ≤ 24 then 896
  else if i.val = 25 then 3712
  else if i.val = 26 then 928 else 0

def semanticTag (i : Fin 27) : UInt8 :=
  if i.val = 2 then 1 else if i.val = 14 then 3
  else if 15 ≤ i.val ∧ i.val ≤ 24 then 2
  else if i.val = 25 then 4 else if i.val = 26 then 5 else 0

def openingSize (i : Fin 4) : Nat :=
  if i.val = 0 then 928 else if i.val = 1 then 32 else if i.val = 2 then 224 else 256

structure Wire where
  semantic : (i : Fin 27) → Vector UInt8 (semanticSize i)
  opening : (i : Fin 4) → Vector UInt8 (openingSize i)
  final : Vector UInt8 2048
  publicBytes : List UInt8
  tag : UInt8

def framed (w : Wire) (i : Fin 27) : List UInt8 :=
  [semanticTag i] ++ le32 (semanticSize i) ++ (w.semantic i).toList

def rest (w : Wire) : Rest where
  framed := framed w
  payload := fun i => (w.opening i).toList
  final := w.final.toList
  pubB := w.publicBytes
  vtag := w.tag

theorem framed_length (w : Wire) (i : Fin 27) :
    (framed w i).length = 5 + semanticSize i := by
  simp [framed, le32]
  omega

theorem framed_safe (w : Wire) (i : Fin 27) :
    (framed w i).length ≠ 31 ∧ (framed w i).length ≠ 65 := by
  rw [framed_length]
  unfold semanticSize
  split <;> (try split) <;> (try split) <;> (try split) <;> omega

theorem opening_safe (w : Wire) (i : Fin 4) :
    ((rest w).payload i).length ≠ 27 := by
  change (w.opening i).toList.length ≠ 27
  simp only [Vector.length_toList]
  unfold openingSize
  split <;> (try split) <;> (try split) <;> omega

theorem transcriptNodeLengths (w : Wire) : TranscriptNodeLengths (rest w) := by
  refine ⟨fun i => (framed_safe w i).1, opening_safe w, ?_⟩
  change w.final.toList.length ≠ 27
  simp

theorem node_ne_concrete_transcript (w : Wire) (answers : GamesR1PBin.RIdx → OracleAnswer)
    (ch : Fin 2 → GamesR1PBin.RIdx) (j : TRead) (f : OracleAnswer) :
    nodeBytes answers ch ≠ addrWith j f (rest w) :=
  nodeBytes_ne_transcript answers ch j f (rest w) (transcriptNodeLengths w)

#print axioms framed_length
#print axioms framed_safe
#print axioms opening_safe
#print axioms transcriptNodeLengths
#print axioms node_ne_concrete_transcript
end R1Z.WireLengthsR1PBin
