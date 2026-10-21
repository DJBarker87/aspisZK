import OraclePortCheckpointSlicesC5

/-! Strict typed prepared-field decoder for the frozen checkpoint offsets.
This is the mathematical codec, not an extracted Rust parser refinement. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCheckpointPreparedC5
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open OraclePortCompactDraft OraclePortCheckpointAbiC5 OraclePortCheckpointSlicesC5

/-- Four bytes only; the proof is symbolic in the encoded numeral. -/
theorem little_le32 (n : Nat) (bound : n < 4294967296) : little (le32 n) = n := by
  norm_num [le32,little,List.range_succ]
  omega

def decodeQuery (b : Bytes) : Option (Fin 262144) :=
  if h : little b < 262144 then some ⟨little b,h⟩ else none

theorem decodeQuery_encode (q : Fin 262144) : decodeQuery (le32 q.val) = some q := by
  have same := little_le32 q.val (by have h := q.isLt; omega)
  simp only [decodeQuery,same,dif_pos q.isLt]

def decodeQueries (b : Bytes) : Option (Fin 22 → Fin 262144) :=
  FixedWidthDecoder.decode decodeQuery 4 22 b

theorem decodeQueries_encode (q : Fin 22 → Fin 262144) :
    decodeQueries (queryBytes q) = some q := by
  exact FixedWidthDecoder.decode_encode decodeQuery (fun i : Fin 262144 => le32 i.val) 4 22 q
    (fun i => by simp only [le32,List.length_map,List.length_range]) decodeQuery_encode

def decode (ck : Bytes) : Option Prepared := do
  let state ← SemanticRecordCodec.decodeState (slice ck 80 32)
  let root0 ← SemanticRecordCodec.decodeState (slice ck 112 32)
  let root1 ← SemanticRecordCodec.decodeState (slice ck 144 32)
  let gamma ← FoldedLeafCodec.decodeWide (slice ck 176 32)
  let kappa ← FoldedLeafCodec.decodeWide (slice ck 208 32)
  let alpha0 ← FoldedLeafCodec.decodeWide (slice ck 240 32)
  let alpha1 ← FoldedLeafCodec.decodeWide (slice ck 272 32)
  let rho ← ExactLeafFieldCodec.decodeQM31 (slice ck 304 16)
  let queries ← decodeQueries (slice ck 320 88)
  let semanticAlpha ← decodeKs 10 (slice ck 408 160)
  let coordinates ← decodeKs 4 (slice ck 568 64)
  let claim ← FoldedLeafCodec.decodeWide (slice ck 632 32)
  pure ⟨state,(fun i => if i.val = 0 then root0 else root1),gamma,kappa,
    (fun i => if i.val = 0 then alpha0 else alpha1),rho,queries,semanticAlpha,coordinates,claim⟩

theorem fin2_eta {T : Type} (v : Fin 2 → T) :
    (fun i : Fin 2 => if i.val = 0 then v 0 else v 1) = v := by
  funext i
  fin_cases i <;> rfl

theorem decode_encode (H : Bytes → State) (stored pub : Bytes) (p : Prepared)
    (a : QueryAccumulator.State K E) : decode (encode H stored pub p a) = some p := by
  obtain ⟨_,_,_,state,root0,root1,gamma,kappa,alpha0,alpha1⟩ := prefix_slices H stored pub p a
  obtain ⟨rho,queries,semanticAlpha,coordinates,claim⟩ := prepared_slices H stored pub p a
  simp only [decode,state,root0,root1,gamma,kappa,alpha0,alpha1,rho,queries,
    semanticAlpha,coordinates,claim,encodeE,encodeK,
    SemanticRecordCodec.decodeState_bytes,FoldedLeafCodec.decodeWide_encode,
    ExactLeafFieldCodec.decodeQM31_encodeQM31,decodeQueries_encode,decodeKs_encode,
    Option.bind_eq_bind,Option.bind_some,fin2_eta]
  rfl

#print axioms little_le32
#print axioms decodeQuery_encode
#print axioms decodeQueries_encode
#print axioms fin2_eta
#print axioms decode_encode
end AspisR1.OraclePortCheckpointPreparedC5
end
