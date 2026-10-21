import OraclePortStoredParserC4

/-! Symbolic encoder/parser roundtrip for honest semantic framing. The proof
recurses on the number of records, not on a large concrete byte string. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortHonestRowsC4
open AspisV8R19.DuplexFrames
open OraclePortCompactDraft
attribute [local instance] Classical.propDecidable

def tagByte (tag : Nat) : AspisV8R19.DuplexFrames.Byte := ⟨tag % 256,Nat.mod_lt _ (by decide)⟩
def header (row : Nat) : AspisV8R19.DuplexFrames.Bytes := tagByte (rowShape row).1 :: le32 (rowShape row).2
def storedSize (row : Nat) : Nat :=
  if 14 ≤ row then (rowShape row).2 / 2 else (rowShape row).2

theorem header_length (row : Nat) : (header row).length = 5 := by
  simp only [header,le32,List.length_cons,List.length_map,List.length_range]

theorem little_zeros (n : Nat) : little (List.replicate n (0 : AspisV8R19.DuplexFrames.Byte)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ,little,List.foldr_cons] at *; rw [ih]; rfl

theorem canonical_zeros (n : Nat) (h : n % 4 = 0) :
    canonical (List.replicate n (0 : AspisV8R19.DuplexFrames.Byte)) := by
  refine ⟨by simpa only [List.length_replicate] using h,?_⟩
  intro j _
  simp only [slice,List.drop_replicate,List.take_replicate,little_zeros]
  decide

theorem storedSize_mod (row : Nat) : storedSize row % 4 = 0 := by
  unfold storedSize
  split <;> (unfold rowShape; split_ifs <;> norm_num)

/-- One parser step, exposing only the small framing operations. -/
theorem semantic_cons (fuel row : Nat) (payload tail : AspisV8R19.DuplexFrames.Bytes) (rs : List Bytes)
    (hp : payload.length = storedSize row)
    (hc : 14 ≤ row → canonical payload)
    (ht : semanticRows fuel (row+1) tail = some rs) :
    semanticRows (fuel+1) row ((header row ++ payload) ++ tail) =
      some ((header row ++ (if 14 ≤ row then expand ((rowShape row).2/32) payload
        else payload)) :: rs) := by
  have hh := header_length row
  have hl : 5 + storedSize row ≤ ((header row ++ payload) ++ tail).length := by
    simp only [List.length_append,hp,hh]; omega
  have hhead : (((header row ++ payload) ++ tail).take 5) = header row := by
    rw [List.append_assoc, ← hh,List.take_append_length]
  have hpay : slice ((header row ++ payload) ++ tail) 5 (storedSize row) = payload := by
    unfold slice
    rw [List.append_assoc, ← hh,List.drop_append_length,← hp, List.take_append_length]
  have htail : ((header row ++ payload) ++ tail).drop (5+storedSize row) = tail := by
    have len : (header row ++ payload).length = 5+storedSize row := by
      simp only [List.length_append,hh,hp]
    rw [← len,List.drop_append_length]
  rw [semanticRows]
  dsimp only
  change (if _ then none else _) = _
  rw [if_neg (by change ¬ _ < 5 + storedSize row; omega)]
  change (if _ then none else _) = _
  rw [hhead,if_neg (by intro h; exact h rfl)]
  change (if _ then none else _) = _
  have notBad : ¬ (14 ≤ row ∧ ¬ canonical (slice ((header row ++ payload) ++ tail) 5 (storedSize row))) := by
    rw [hpay]; exact fun h => h.2 (hc h.1)
  unfold storedSize at notBad
  rw [if_neg notBad]
  change (do
    let rest ← semanticRows fuel (row+1) (((header row ++ payload) ++ tail).drop (5+storedSize row))
    pure ((((header row ++ payload) ++ tail).take 5 ++
      (if 14 ≤ row then expand ((rowShape row).2/32)
        (slice ((header row ++ payload) ++ tail) 5 (storedSize row))
       else slice ((header row ++ payload) ++ tail) 5 (storedSize row))) :: rest)) = _
  rw [htail,ht]
  simp only [hhead,hpay]; rfl

def encode : Nat → Nat → Bytes
  | 0, _ => []
  | n+1, row => (header row ++ List.replicate (storedSize row) 0) ++ encode n (row+1)

def decoded : Nat → Nat → List Bytes
  | 0, _ => []
  | n+1, row => (header row ++ (if 14 ≤ row then
      expand ((rowShape row).2/32) (List.replicate (storedSize row) 0)
      else List.replicate (storedSize row) 0)) :: decoded n (row+1)

theorem roundtrip (n row : Nat) : semanticRows n row (encode n row) = some (decoded n row) := by
  induction n generalizing row with
  | zero => simp only [encode,decoded,semanticRows,↓reduceIte]
  | succ n ih =>
    exact semantic_cons n row _ _ _ (List.length_replicate ..)
      (fun _ => canonical_zeros _ (storedSize_mod row)) (ih (row+1))

#print axioms header_length
#print axioms little_zeros
#print axioms canonical_zeros
#print axioms storedSize_mod
#print axioms semantic_cons
#print axioms roundtrip
end AspisR1.OraclePortHonestRowsC4
end
