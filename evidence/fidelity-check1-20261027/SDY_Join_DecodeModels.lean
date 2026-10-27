import SDY_Join_ABI
open Aeneas Aeneas.Std Result ControlFlow Error
open SDY_Join_Release SDY_Join_FieldExternal
/- XRg_decode_reference: row gate, checked usize range, framed[5..],
   then canonical four-limb decoding. Validation token/P6/heap bridge OPEN. -/
def r1_wire.ValidatedRecord.decode_k (N : Usize) (r : r1_wire.ValidatedRecord) (offset : Usize) :
    Result (core.result.Result (Array aspis_core.field.QM31 N) r1_wire.Error) := do
  if r.row < 14#u8 then ok (.Err .InvalidRow) else do
    let start := offset.val * 32
    let size := N.val * 32
    let finish := start + size
    if start > Usize.max ∨ size > Usize.max ∨ finish > Usize.max then ok (.Err (.Length r.row)) else do
      if r.framed.val.length < 5 then fail .panic else do
        let payload := r.framed.val.drop 5
        if finish > payload.length then ok (.Err (.Length r.row)) else do
          let values := (List.range N.val).map fun i =>
            let bs := (payload.drop (start+32*i)).take 16
            let xs := (List.range 4).map fun j => SDY_Join_word ((bs.drop (4*j)).take 4)
            (xs.all (fun x => x < 2147483647#u32),SDY_Join_q xs)
          match (List.range N.val).find? (fun i => !(values[i]?.getD (true,qzero)).1) with
          | some i =>
            dite (offset.val+i ≤ UScalar.cMax .Usize)
              (fun h => ok (.Err (.NonCanonical r.row (UScalar.ofNat (offset.val+i) h))))
              (fun _ => fail .panic)
          | none =>
            let xs := values.map Prod.snd
            dite (xs.length = N.val) (fun h => ok (.Ok ⟨xs,h⟩)) (fun _ => fail .panic)

/- XRg_claims_reference rows[0..2] in order. The owned reference abstracts
   Prefix association and allocation; this model additionally projects the
   actual row25 and decodes the same offsets. P6 OPEN. -/
def r1_semantic.claims (p : r1_wire.Prefix) :
    Result (core.result.Result (Array (Array aspis_core.field.QM31 29#usize) 3#usize) r1_wire.Error) := do
  let framed ← Array.index_usize p.records 25#usize
  let a ← r1_wire.ValidatedRecord.decode_k 29#usize ⟨25#u8,framed⟩ 0#usize
  match a with
  | .Err e => ok (.Err e)
  | .Ok a =>
    let b ← r1_wire.ValidatedRecord.decode_k 29#usize ⟨25#u8,framed⟩ 29#usize
    match b with
    | .Err e => ok (.Err e)
    | .Ok b =>
      let c ← r1_wire.ValidatedRecord.decode_k 29#usize ⟨25#u8,framed⟩ 58#usize
      match c with
      | .Err e => ok (.Err e)
      | .Ok c => ok (.Ok (Array.make 3#usize [a,b,c]))

/- XRg_boundary_reference: coefficient0 appears twice, then 1..27. P6 OPEN. -/
def r1_semantic.semantic_boundary (p : Array aspis_core.field.QM31 28#usize) : Result aspis_core.field.QM31 := do
  let first ← Array.index_usize p 0#usize
  p.val.foldlM aspis_core.field.QM31.add first

/- XRi_reference_wide_view: exact compact offsets and checked slicing.
   Carrier/borrow correspondence and all source P6 remain OPEN. -/
def SDY_Join_sliceRange (bs : Slice U8) (lo hi : Nat) : Result (Slice U8) :=
  if lo ≤ hi ∧ hi ≤ bs.val.length then
    ok ⟨(bs.val.drop lo).take (hi-lo),by
      exact Nat.le_trans (List.length_take_le' _ _) (Nat.le_trans (by simp) bs.property)⟩
  else fail .panic

def verifier.candidate.wide_view (proof semantic y1 : Slice U8) :
    Result (core.result.Result verifier.View verifier.Error) := do
  let inactiveBytes ← SDY_Join_sliceRange proof 7495 7527
  let inactive ← aspis_core.field.wide_exact.WideExact.from_le_bytes inactiveBytes
  match inactive with
  | none => ok (.Err .Parse)
  | some inactive =>
    let round0 ← SDY_Join_sliceRange proof 7527 7751
    let root ← SDY_Join_sliceRange proof 7751 7783
    let root ← dite (root.val.length = 32) (fun h => ok (⟨root.val,h⟩ : Array U8 32#usize)) (fun _ => fail .panic)
    let round1 ← SDY_Join_sliceRange proof 7783 8007
    let final_message ← SDY_Join_sliceRange proof 8007 10055
    ok (.Ok {
      variant := .S2
      semantic := semantic
      y1 := y1
      inactive := inactive
      round0 := round0
      folded_root := some root
      round1 := round1
      final_message := final_message
      query_bytes := ⟨[],by decide⟩ })
