import OraclePortCheckpointStateC3
import OraclePortPhysicalFrameDraft
import R1SelectedFieldSequenceCodec

/-! Physical 1768-byte model serializer with no caller-supplied accumulator.
The accumulator written at offsets 664..1736 is the reached ten-step state.
This is a byte-model composition, not a frozen-Rust refinement theorem. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCheckpointAbiC5
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortCheckpointStateC3
abbrev K := ExactLeafFieldCodec.QM31Exact
abbrev E := LiteralTranscript.E

structure Prepared where
  state : State
  roots : Fin 2 → State
  gamma : E
  kappa : E
  alpha : Fin 2 → E
  rho : K
  queries : Fin 22 → Fin 262144
  semanticAlpha : Fin 10 → K
  coordinates : Fin 4 → K
  claim : E

def encodeK (x : K) : Bytes := ExactLeafFieldCodec.encodeQM31 x
def encodeE (x : E) : Bytes := FoldedLeafCodec.encodeWide x
def encodeKs {n : Nat} (v : Fin n → K) : Bytes := FixedWidthDecoder.encode encodeK v
def decodeKs (n : Nat) (b : Bytes) : Option (Fin n → K) :=
  FixedWidthDecoder.decode ExactLeafFieldCodec.decodeQM31 16 n b

theorem encodeK_length (x : K) : (encodeK x).length = 16 :=
  ExactLeafFieldCodec.encodeQM31_length x

theorem encodeKs_length {n : Nat} (v : Fin n → K) : (encodeKs v).length = n*16 := by
  induction n with
  | zero => simp only [encodeKs,FixedWidthDecoder.encode,List.ofFn_zero,List.flatMap_nil]; rfl
  | succ n ih =>
    change ((List.ofFn v).flatMap encodeK).length = _
    rw [List.ofFn_succ,List.flatMap_cons,List.length_append,encodeK_length]
    have h := ih (fun i => v i.succ)
    change ((List.ofFn (fun i => v i.succ)).flatMap encodeK).length = n*16 at h
    rw [h]; omega

theorem decodeKs_encode {n : Nat} (v : Fin n → K) : decodeKs n (encodeKs v) = some v :=
  FixedWidthDecoder.decode_encode _ _ 16 n v encodeK_length ExactLeafFieldCodec.decodeQM31_encodeQM31

def queryBytes (q : Fin 22 → Fin 262144) : Bytes :=
  (List.ofFn q).flatMap (fun i => le32 i.val)

theorem queryBytes_length (q : Fin 22 → Fin 262144) : (queryBytes q).length = 88 := by
  have generic (n : Nat) (f : Fin n → Nat) :
      ((List.ofFn f).flatMap le32).length = n*4 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.ofFn_succ,List.flatMap_cons,List.length_append]
      simp only [le32,List.length_map,List.length_range]
      rw [ih]; omega
  exact generic 22 (fun j => (q j).val)

/-- Each block has precisely the frozen field width, including the full
prepared challenges and query vector. Header fixes saved.next = 10. -/
def blocks (p : Prepared) (a : QueryAccumulator.State K E)
    (proofHash publicHash : State) : List Bytes :=
  [OraclePortPhysicalFrameDraft.magic ++ [2,10,1,0,0,0,0,0],
   bytes proofHash,bytes publicHash,bytes p.state,bytes (p.roots 0),bytes (p.roots 1),
   encodeE p.gamma,encodeE p.kappa,encodeE (p.alpha 0),encodeE (p.alpha 1),
   encodeK p.rho,queryBytes p.queries,encodeKs p.semanticAlpha,encodeKs p.coordinates,
   encodeE p.claim,encodeE a.rhs,encodeK a.power,encodeKs a.weights]

def widths : List Nat := [16,32,32,32,32,32,32,32,32,32,16,88,160,64,32,32,16,1024]
def offsets : List Nat := [0,16,48,80,112,144,176,208,240,272,304,320,408,568,632,664,696,712]

theorem block_widths (p : Prepared) (a : QueryAccumulator.State K E) (hp hu : State) :
    (blocks p a hp hu).map List.length = widths := by
  simp only [blocks,widths,List.map_cons,List.map_nil,encodeE,FoldedLeafCodec.encodeWide_length,
    encodeK_length,encodeKs_length,queryBytes_length]
  rfl

def body (p : Prepared) (a : QueryAccumulator.State K E) (hp hu : State) : Bytes :=
  (blocks p a hp hu).flatten

theorem body_length (p : Prepared) (a : QueryAccumulator.State K E) (hp hu : State) :
    (body p a hp hu).length = 1736 := by
  rw [body,List.length_flatten,block_widths]
  rfl

def encode (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) : Bytes :=
  let b := body p a (H stored) (H pub)
  b ++ bytes (H (OraclePortPhysicalFrameDraft.domain ++ b))

theorem encode_length (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) : (encode H stored pub p a).length = 1768 := by
  simp only [encode,List.length_append,body_length]
  rfl

/-- Structural field extraction; no large encoded vector is reduced. -/
theorem slice_block (before field after : Bytes) :
    slice (before ++ field ++ after) before.length field.length = field := by
  rw [slice,List.append_assoc,List.drop_append_length,List.take_append_length]

/-- The checksum is over the entire 1736-byte body, including reached state. -/
theorem checksum_bound (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) :
    (encode H stored pub p a).take 1736 = body p a (H stored) (H pub) ∧
    (encode H stored pub p a).drop 1736 =
      bytes (H (OraclePortPhysicalFrameDraft.domain ++ body p a (H stored) (H pub))) := by
  constructor
  · simpa only [encode,body_length] using
      (@List.take_append_length _ (body p a (H stored) (H pub))
        (bytes (H (OraclePortPhysicalFrameDraft.domain ++ body p a (H stored) (H pub)))))
  · simpa only [encode,body_length] using
      (@List.drop_append_length _ (body p a (H stored) (H pub))
        (bytes (H (OraclePortPhysicalFrameDraft.domain ++ body p a (H stored) (H pub)))))

#print axioms encodeK_length
#print axioms encodeKs_length
#print axioms decodeKs_encode
#print axioms queryBytes_length
#print axioms block_widths
#print axioms body_length
#print axioms encode_length
#print axioms slice_block
#print axioms checksum_bound
end AspisR1.OraclePortCheckpointAbiC5
end
