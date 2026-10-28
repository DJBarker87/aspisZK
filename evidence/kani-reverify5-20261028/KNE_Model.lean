import LPm_CheckpointProgram
import KND_Schedule
set_option autoImplicit false
noncomputable section
namespace AspisR1.KNE_Model
open Aeneas Aeneas.Std
open CheckpointBytes5Writer CheckpointBytesBlocks CheckpointBytesBody CheckpointBytesDigest
open CheckpointBytesE MultiproofConeCanonical OraclePortCkptAbi4Decode OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

-- Individual native writes, obtained by refining the adopted field blocks.
def indexed {n : Nat} (stem : String) (f : Fin n → Bytes) : List (String × Bytes) :=
  List.ofFn (fun i => (stem ++ toString i.val, f i))

def bodyEmissions (f : Fields) (hp hu : State) : List (String × Bytes) :=
  [("magic",OraclePortPhysicalFrameDraft.magic),("header",[2,10,1,0,0,0,0,0]),
   ("proof_digest",bytes hp),("public_digest",bytes hu),("state",bytes f.state),
   ("root0",bytes (f.roots 0)),("root1",bytes (f.roots 1)),
   ("gamma",bytesOf (rawBytes f.gamma)),("kappa",bytesOf (rawBytes f.kappa)),
   ("alpha0",bytesOf (rawBytes (f.alpha 0))),("alpha1",bytesOf (rawBytes (f.alpha 1))),
   ("rho",rawK f.rho)] ++
  indexed "query" (fun i => le32 (f.queries i).val) ++
  indexed "semantic" (fun i => rawK (f.semanticAlpha i)) ++
  indexed "z" (fun i => rawK (f.coordinates i)) ++
  [("claim",bytesOf (rawBytes f.claim)),("rhs",bytesOf (rawBytes f.rhs)),
   ("power",rawK f.power)] ++ indexed "weight" (fun i => rawK (f.weights i))

def payload (es : List (String × Bytes)) : Bytes := (es.map Prod.snd).flatten
def shape (es : List (String × Bytes)) : List (String × Nat) :=
  es.map (fun e => (e.1,e.2.length))

theorem indexed_payload {n : Nat} (stem : String) (f : Fin n → Bytes) :
    (indexed stem f).map Prod.snd = List.ofFn f := by
  simp only [indexed,List.map_ofFn,Function.comp_def]

theorem indexed_shape {n : Nat} (stem : String) (f : Fin n → Bytes) (w : Nat)
    (width : ∀ i, (f i).length = w) :
    shape (indexed stem f) = (List.range n).map (fun i => (stem ++ toString i,w)) := by
  apply List.ext_getElem
  · simp [shape,indexed]
  · intro i hi hj
    simp [shape,indexed,width]

theorem rawK_length (q : OraclePortCkptAbi2Extracted.aspis_core.field.QM31) : (rawK q).length = 16 := by
  simp [rawK,bytesOf,CheckpointP6EncodeK.bytes,core.num.U32.to_le_bytes,BitVec.toLEBytes]

theorem flatten_ofFn {α : Type} {n : Nat} (f : Fin n → α) (g : α → Bytes) :
    (List.ofFn (fun i => g (f i))).flatten = (List.ofFn f).flatMap g := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ,List.flatten_cons,List.flatMap_cons]
    rw [ih]

-- The decomposition is tied to the adopted byte model, not a second width list.
theorem bodyEmissions_payload (f : Fields) (hp hu : State) :
    payload (bodyEmissions f hp hu) = CheckpointBytesBlocks.body f hp hu := by
  have query := flatten_ofFn f.queries (fun q => le32 q.val)
  simp only [payload,bodyEmissions,List.map_append,List.map_cons,List.map_nil,
    List.flatten_append,indexed_payload,List.flatten_cons,List.flatten_nil,
    List.append_nil,CheckpointBytesBlocks.body,blocks,rawKs,
    OraclePortCheckpointAbiC5.queryBytes,query,flatten_ofFn,
    List.append_assoc]

theorem bodyEmissions_shape (f : Fields) (hp hu : State) :
    shape (bodyEmissions f hp hu) = KND_Schedule.emissions.take 115 := by
  have qwidth (i : Fin 22) : (le32 (f.queries i).val).length = 4 := by
    simp [le32]
  simp only [bodyEmissions,shape,List.map_append,List.map_cons,List.map_nil]
  change _ ++ shape (indexed "query" _) ++ shape (indexed "semantic" _) ++
    shape (indexed "z" _) ++ _ ++ shape (indexed "weight" _) = _
  rw [indexed_shape _ _ 4 qwidth,indexed_shape _ _ 16 (fun _ => rawK_length _),
    indexed_shape _ _ 16 (fun _ => rawK_length _),
    indexed_shape _ _ 16 (fun _ => rawK_length _)]
  simp only [bytesOf,List.length_map,rawBytes_length,rawK_length]
  rfl

#print axioms indexed_payload
#print axioms indexed_shape
#print axioms flatten_ofFn
#print axioms rawK_length
#print axioms bodyEmissions_payload
#print axioms bodyEmissions_shape
end AspisR1.KNE_Model
end
