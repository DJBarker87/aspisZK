import R1SemanticRecordCodec
import R1TypedPrefixParser
set_option autoImplicit false
namespace AspisR1.SemanticPrefixCodec

abbrev Bytes := SemanticRecordCodec.Bytes

structure At (row : Nat) where
  isLt : row < 25
  value : SemanticRecordCodec.RowPayload ⟨row, isLt⟩

abbrev Entry := Sigma At
abbrev Full := (i : Fin 25) → SemanticRecordCodec.RowPayload i

def decodeOne (row : Nat) (raw : Bytes) : Option (At row) :=
  if h : row < 25 then
    (SemanticRecordCodec.decode ⟨row, h⟩ raw).map (fun value => ⟨h, value⟩)
  else none

def decodeFrom (row : Nat) (raws : List Bytes) : Option (List Entry) :=
  TypedPrefixParser.decode decodeOne row raws

def encodeEntry (entry : Entry) : Bytes :=
  SemanticRecordCodec.encode entry.2.value

def entriesOf (values : Full) : List Entry :=
  List.ofFn (fun i : Fin 25 => (⟨i.val, ⟨i.isLt, values i⟩⟩ : Entry))

def encodeFull (values : Full) : List Bytes :=
  (entriesOf values).map encodeEntry

-- The list parser accepts [] at any starting row. A nonempty list starting
-- at row >= 25 fails. A full25 interface additionally requires length = 25.
-- At stores a logical row proof; encodeEntry does not add a wire row tag.



theorem decodeOne_reject (row : Nat) (h : 25 ≤ row) (raw : Bytes) :
    decodeOne row raw = none := by
  simp [decodeOne, show ¬ row < 25 by omega]

theorem decodeFrom_reject (row : Nat) (h : 25 ≤ row)
    (raw : Bytes) (rest : List Bytes) :
    decodeFrom row (raw :: rest) = none := by
  simp [decodeFrom, TypedPrefixParser.decode, decodeOne_reject row h raw]

theorem decodeOne_encode (row : Nat) (value : At row) :
    decodeOne row (SemanticRecordCodec.encode value.value) = some value := by
  rcases value with ⟨h, value⟩
  simp [decodeOne, h, SemanticRecordCodec.decode_encode]

theorem encode_of_decodeOne (row : Nat) (raw : Bytes) (value : At row)
    (h : decodeOne row raw = some value) :
    SemanticRecordCodec.encode value.value = raw := by
  rcases value with ⟨hlt, value⟩
  simp only [decodeOne, dif_pos hlt] at h
  cases hd : SemanticRecordCodec.decode ⟨row, hlt⟩ raw with
  | none => simp [hd] at h
  | some decoded =>
      have he : (At.mk hlt decoded : At row) = At.mk hlt value := by
        simpa [hd] using h
      cases he
      exact SemanticRecordCodec.encode_of_decode _ _ _ hd

theorem prefix_stable (row : Nat) (preRaw suffix : List Bytes)
    (out : List Entry) (h : decodeFrom row (preRaw ++ suffix) = some out) :
    decodeFrom row preRaw = some (out.take preRaw.length) :=
  TypedPrefixParser.prefix_stable decodeOne row preRaw suffix out h

theorem failure_persists (row : Nat) (preRaw suffix : List Bytes)
    (h : decodeFrom row preRaw = none) :
    decodeFrom row (preRaw ++ suffix) = none :=
  TypedPrefixParser.failure_persists decodeOne row preRaw suffix h

theorem decode_encode_entries (row : Nat) (out : List Entry)
    (hrows : out.map Sigma.fst = List.range' row out.length) :
    decodeFrom row (out.map encodeEntry) = some out := by
  induction out generalizing row with
  | nil => rfl
  | cons entry tail ih =>
      rcases entry with ⟨j, value⟩
      simp only [List.map_cons, List.length_cons, List.range'_succ] at hrows
      have hj : j = row := (List.cons.inj hrows).1
      subst j
      have ht := (List.cons.inj hrows).2
      have ht' := ih (row + 1) ht
      unfold decodeFrom at ht'
      simpa [decodeFrom, TypedPrefixParser.decode, encodeEntry,
        decodeOne_encode, ht']

theorem decoded_index (raws : List Bytes) (out : List Entry)
    (hlen : raws.length = 25) (h : decodeFrom 0 raws = some out)
    (i : Fin 25) :
    (out[i.val]'(by
      have hh := TypedPrefixParser.decode_length decodeOne 0 raws out h
      omega)).1 = i.val := by
  have hl := TypedPrefixParser.decode_length decodeOne 0 raws out h
  have hi : i.val < out.length := by omega
  have hr := TypedPrefixParser.decode_rows decodeOne 0 raws out h
  have hg := congrArg (fun xs : List Nat => xs[i.val]?) hr
  rw [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_range' (by omega)] at hg
  simpa using hg

def fullOfDecoded (raws : List Bytes) (out : List Entry)
    (hlen : raws.length = 25) (h : decodeFrom 0 raws = some out) : Full :=
  fun i => by
    have hl := TypedPrefixParser.decode_length decodeOne 0 raws out h
    let entry : Entry := out[i.val]'(by omega)
    have hi : (⟨entry.1, entry.2.isLt⟩ : Fin 25) = i :=
      Fin.ext (decoded_index raws out hlen h i)
    exact hi ▸ entry.2.value

def decodeFull (raws : List Bytes) : Option Full :=
  if hlen : raws.length = 25 then
    match h : decodeFrom 0 raws with
    | none => none
    | some out => some (fullOfDecoded raws out hlen h)
  else none

theorem decodeFull_of_decoded (raws : List Bytes) (out : List Entry)
    (hlen : raws.length = 25) (h : decodeFrom 0 raws = some out) :
    decodeFull raws = some (fullOfDecoded raws out hlen h) := by
  unfold decodeFull
  rw [dif_pos hlen]
  split
  · rename_i hnone
    simp_all
  · rename_i decoded hdecoded
    have he : decoded = out := Option.some.inj (hdecoded.symm.trans h)
    subst decoded
    rfl

theorem decodeFull_wrong_length (raws : List Bytes) (h : raws.length ≠ 25) :
    decodeFull raws = none := by
  simp [decodeFull, h]

theorem entriesOf_length (values : Full) : (entriesOf values).length = 25 := by
  simp [entriesOf]

theorem entriesOf_rows (values : Full) :
    (entriesOf values).map Sigma.fst = List.range' 0 25 := by
  apply List.ext_getElem
  · simp only [List.length_map, entriesOf, List.length_ofFn, List.length_range']
  · intro i hi hj
    simp only [List.getElem_map, entriesOf, List.getElem_ofFn,
      List.getElem_range', Nat.zero_add, Nat.one_mul]

theorem encodeFull_length (values : Full) : (encodeFull values).length = 25 := by
  simp [encodeFull, entriesOf]

theorem decode_encodeFull (values : Full) :
    decodeFrom 0 (encodeFull values) = some (entriesOf values) := by
  apply decode_encode_entries
  simpa only [entriesOf_length] using entriesOf_rows values

theorem entriesOf_getElem (values : Full) (i : Fin 25) :
    (entriesOf values)[i.val]'(by rw [entriesOf_length]; exact i.isLt) =
      (⟨i.val, ⟨i.isLt, values i⟩⟩ : Entry) := by
  exact List.getElem_ofFn _

theorem payload_val_transport {i j : Fin 25} (h : i = j)
    (value : SemanticRecordCodec.RowPayload i) :
    ((h ▸ value) : SemanticRecordCodec.RowPayload j).val = value.val := by
  cases h
  rfl

theorem encode_transport {i j : Fin 25} (h : i = j)
    (value : SemanticRecordCodec.RowPayload i) :
    SemanticRecordCodec.encode ((h ▸ value) : SemanticRecordCodec.RowPayload j) =
      SemanticRecordCodec.encode value := by
  cases h
  rfl

theorem fullOfDecoded_encodeFull (values : Full) :
    fullOfDecoded (encodeFull values) (entriesOf values)
      (encodeFull_length values) (decode_encodeFull values) = values := by
  funext i
  apply Subtype.ext
  dsimp only [fullOfDecoded]
  rw [payload_val_transport]
  exact congrArg (fun e : Entry => e.2.value.val) (entriesOf_getElem values i)

theorem decodeFull_encodeFull (values : Full) :
    decodeFull (encodeFull values) = some values := by
  rw [decodeFull_of_decoded (encodeFull values) (entriesOf values)
    (encodeFull_length values) (decode_encodeFull values)]
  rw [fullOfDecoded_encodeFull]

theorem encode_of_decodeFrom (row : Nat) (raws : List Bytes) (out : List Entry)
    (h : decodeFrom row raws = some out) : out.map encodeEntry = raws := by
  induction raws generalizing row out with
  | nil =>
      have he : ([] : List Entry) = out := by
        simpa [decodeFrom, TypedPrefixParser.decode] using h
      rw [← he]
      rfl
  | cons raw rest ih =>
      cases hfirst : decodeOne row raw with
      | none => simp [decodeFrom, TypedPrefixParser.decode, hfirst] at h
      | some value =>
          cases hrest : decodeFrom (row + 1) rest with
          | none =>
              have ht : TypedPrefixParser.decode decodeOne (row + 1) rest = none := hrest
              simp [decodeFrom, TypedPrefixParser.decode, hfirst, ht] at h
          | some tail =>
              have ht : TypedPrefixParser.decode decodeOne (row + 1) rest = some tail := hrest
              have he : (⟨row, value⟩ :: tail : List Entry) = out := by
                simpa [decodeFrom, TypedPrefixParser.decode, hfirst, ht] using h
              rw [← he]
              change SemanticRecordCodec.encode value.value :: tail.map encodeEntry = raw :: rest
              rw [encode_of_decodeOne row raw value hfirst, ih (row + 1) tail hrest]

theorem encode_fullOfDecoded (raws : List Bytes) (out : List Entry)
    (hlen : raws.length = 25) (h : decodeFrom 0 raws = some out) :
    encodeFull (fullOfDecoded raws out hlen h) = raws := by
  have hback := encode_of_decodeFrom 0 raws out h
  have houtlen := TypedPrefixParser.decode_length decodeOne 0 raws out h
  calc
    encodeFull (fullOfDecoded raws out hlen h) = out.map encodeEntry := by
      apply List.ext_getElem
      · rw [encodeFull_length, List.length_map]
        omega
      · intro i hi hj
        have hi25 : i < 25 := by simpa only [encodeFull_length] using hi
        simp only [encodeFull, List.getElem_map]
        change encodeEntry ((entriesOf (fullOfDecoded raws out hlen h))[i]) =
          encodeEntry (out[i])
        calc
          _ = SemanticRecordCodec.encode (fullOfDecoded raws out hlen h ⟨i, hi25⟩) :=
            congrArg encodeEntry (entriesOf_getElem (fullOfDecoded raws out hlen h) ⟨i, hi25⟩)
          _ = _ := by
            dsimp only [fullOfDecoded]
            exact encode_transport _ _
    _ = raws := hback

theorem encodeFull_of_decodeFull (raws : List Bytes) (values : Full)
    (h : decodeFull raws = some values) : encodeFull values = raws := by
  unfold decodeFull at h
  split at h
  · rename_i hlen
    split at h
    · simp at h
    · rename_i out hout
      have he : fullOfDecoded raws out hlen hout = values := Option.some.inj h
      rw [← he]
      exact encode_fullOfDecoded raws out hlen hout
  · simp at h

#print axioms encode_of_decodeFrom
#print axioms encode_fullOfDecoded
#print axioms encodeFull_of_decodeFull
#print axioms decodeOne_reject
#print axioms decodeFrom_reject
#print axioms decodeOne_encode
#print axioms encode_of_decodeOne
#print axioms prefix_stable
#print axioms failure_persists
#print axioms decode_encode_entries
#print axioms decoded_index
#print axioms decodeFull_wrong_length
#print axioms entriesOf_rows
#print axioms decode_encodeFull
#print axioms decodeFull_encodeFull
end AspisR1.SemanticPrefixCodec
