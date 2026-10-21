import CheckpointBytesEC5

set_option autoImplicit false
noncomputable section
namespace AspisR1.CheckpointBytesBlocks
open Aeneas Aeneas.Std Result
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCkptAbi4Decode OraclePortCkptAbi5Codec MultiproofConeCanonical
open OraclePortCompactDraft CheckpointBytesE CheckpointBytesEC5

/-- A raw scalar inventory for the fixed body. This is a reference carrier;
identifying its fields with a reached production state is separate. -/
structure Fields where
  state : State
  roots : Fin 2 → State
  gamma : RawE
  kappa : RawE
  alpha : Fin 2 → RawE
  rho : RawK
  queries : Fin 22 → Fin 262144
  semanticAlpha : Fin 10 → RawK
  coordinates : Fin 4 → RawK
  claim : RawE
  rhs : RawE
  power : RawK
  weights : Fin 64 → RawK

structure CanonicalFields (f : Fields) : Prop where
  gamma : CanonicalWide f.gamma
  kappa : CanonicalWide f.kappa
  alpha : ∀ j, CanonicalWide (f.alpha j)
  rho : Canonical f.rho
  semanticAlpha : ∀ j, Canonical (f.semanticAlpha j)
  coordinates : ∀ j, Canonical (f.coordinates j)
  claim : CanonicalWide f.claim
  rhs : CanonicalWide f.rhs
  power : Canonical f.power
  weights : ∀ j, Canonical (f.weights j)

def prepared (f : Fields) (h : CanonicalFields f) : OraclePortCheckpointAbiC5.Prepared :=
  ⟨f.state,f.roots,exactE f.gamma h.gamma,exactE f.kappa h.kappa,
    (fun j => exactE (f.alpha j) (h.alpha j)),exactK f.rho h.rho,f.queries,
    (fun j => exactK (f.semanticAlpha j) (h.semanticAlpha j)),
    (fun j => exactK (f.coordinates j) (h.coordinates j)),exactE f.claim h.claim⟩

def accumulator (f : Fields) (h : CanonicalFields f) :
    QueryAccumulator.State OraclePortCheckpointAbiC5.K OraclePortCheckpointAbiC5.E :=
  ⟨(fun j => exactK (f.weights j) (h.weights j)),exactE f.rhs h.rhs,
    exactK f.power h.power,10⟩

def rawK (q : RawK) : Bytes := bytesOf (CheckpointP6EncodeK.bytes q)
def rawKs {n : Nat} (qs : Fin n → RawK) : Bytes := (List.ofFn qs).flatMap rawK

theorem rawK_c5 (q : RawK) (h : Canonical q) :
    rawK q = OraclePortCheckpointAbiC5.encodeK (exactK q h) := by
  obtain ⟨out,run,layout⟩ := CheckpointP6EncodeK.encode_k_total q
  obtain ⟨out',run',encoded⟩ := CheckpointP6KBytes.encode_k_c5 q h
  rw [run] at run'
  have same := Result.ok.inj run'
  subst out'
  simpa only [layout,rawK] using encoded

theorem rawKs_c5 {n : Nat} (qs : Fin n → RawK) (h : ∀ j, Canonical (qs j)) :
    rawKs qs = OraclePortCheckpointAbiC5.encodeKs (fun j => exactK (qs j) (h j)) := by
  induction n with
  | zero => simp [rawKs,OraclePortCheckpointAbiC5.encodeKs,FixedWidthDecoder.encode]
  | succ n ih =>
    simp only [rawKs,OraclePortCheckpointAbiC5.encodeKs,FixedWidthDecoder.encode,
      List.ofFn_succ,List.flatMap_cons]
    change rawK (qs 0) ++ rawKs (fun j => qs j.succ) =
      OraclePortCheckpointAbiC5.encodeK (exactK (qs 0) (h 0)) ++
      OraclePortCheckpointAbiC5.encodeKs (fun j => exactK (qs j.succ) (h j.succ))
    rw [rawK_c5,ih (fun j => qs j.succ) (fun j => h j.succ)]

/-- Eighteen ordered raw-field blocks, including all 64 weights. -/
def blocks (f : Fields) (hp hu : State) : List Bytes :=
  [OraclePortPhysicalFrameDraft.magic ++ [2,10,1,0,0,0,0,0],
   bytes hp,bytes hu,bytes f.state,bytes (f.roots 0),bytes (f.roots 1),
   bytesOf (rawBytes f.gamma),bytesOf (rawBytes f.kappa),
   bytesOf (rawBytes (f.alpha 0)),bytesOf (rawBytes (f.alpha 1)),
   rawK f.rho,OraclePortCheckpointAbiC5.queryBytes f.queries,
   rawKs f.semanticAlpha,rawKs f.coordinates,bytesOf (rawBytes f.claim),
   bytesOf (rawBytes f.rhs),rawK f.power,rawKs f.weights]

theorem blocks_c5 (f : Fields) (h : CanonicalFields f) (hp hu : State) :
    blocks f hp hu = OraclePortCheckpointAbiC5.blocks (prepared f h) (accumulator f h) hp hu := by
  simp only [blocks,OraclePortCheckpointAbiC5.blocks,prepared,accumulator,
    rawBytes_c5 _ h.gamma,rawBytes_c5 _ h.kappa,
    rawBytes_c5 _ (h.alpha 0),rawBytes_c5 _ (h.alpha 1),rawK_c5 _ h.rho,
    rawKs_c5 _ h.semanticAlpha,rawKs_c5 _ h.coordinates,rawBytes_c5 _ h.claim,
    rawBytes_c5 _ h.rhs,rawK_c5 _ h.power,rawKs_c5 _ h.weights]

def body (f : Fields) (hp hu : State) : Bytes := (blocks f hp hu).flatten

theorem body_c5 (f : Fields) (h : CanonicalFields f) (hp hu : State) :
    body f hp hu = OraclePortCheckpointAbiC5.body (prepared f h) (accumulator f h) hp hu := by
  rw [body,OraclePortCheckpointAbiC5.body,blocks_c5]

def encode (H : Bytes → State) (stored pub : Bytes) (f : Fields) : Bytes :=
  let b := body f (H stored) (H pub)
  b ++ bytes (H (OraclePortPhysicalFrameDraft.domain ++ b))

/-- Fixed-block composition plus the checksum on exactly that whole body.
No statement about the production body_byte traversal is assumed or inferred. -/
theorem encode_c5 (H : Bytes → State) (stored pub : Bytes) (f : Fields)
    (h : CanonicalFields f) :
    encode H stored pub f =
      OraclePortCheckpointAbiC5.encode H stored pub (prepared f h) (accumulator f h) := by
  simp only [encode,OraclePortCheckpointAbiC5.encode,body_c5 f h]

#print axioms rawK_c5
#print axioms rawKs_c5
#print axioms blocks_c5
#print axioms body_c5
#print axioms encode_c5
end AspisR1.CheckpointBytesBlocks
end
