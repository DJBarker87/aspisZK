import LPn_Kit_DecodeModels
open Aeneas Aeneas.Std Result LPl_Kit_Release LPl_Kit_FieldExternal
set_option autoImplicit false
namespace LPo.View

-- LPa_Slices proofs, unchanged apart from the adopted LPn nominal carrier.
def segment (bs : Slice U8) (lo hi : Nat) : Slice U8 :=
  ⟨(bs.val.drop lo).take (hi-lo),by
    exact Nat.le_trans (List.length_take_le' _ _) (Nat.le_trans (by simp) bs.property)⟩
theorem range_success (bs : Slice U8) (lo hi : Nat)
    (valid : lo ≤ hi ∧ hi ≤ bs.val.length) :
    LPn_Kit_sliceRange bs lo hi = ok (segment bs lo hi) := by
  simp only [LPn_Kit_sliceRange, if_pos valid]
  rfl
theorem segment_length (bs : Slice U8) (lo hi : Nat)
    (valid : lo ≤ hi ∧ hi ≤ bs.val.length) :
    (segment bs lo hi).val.length = hi-lo := by
  simp only [segment, List.length_take, List.length_drop]
  omega

def root (proof : Slice U8) (len : 10055 ≤ proof.val.length) : Array U8 32#usize :=
  ⟨(segment proof 7751 7783).val,by
    exact segment_length proof 7751 7783 (by omega)⟩

def rest (proof semantic y1 : Slice U8) (len : 10055 ≤ proof.val.length)
    (inactive : LPl_Kit_Wide) : verifier.View :=
  {variant := .S2, semantic := semantic, y1 := y1, inactive := inactive,
   round0 := segment proof 7527 7751, folded_root := some (root proof len),
   round1 := segment proof 7783 8007, final_message := segment proof 8007 10055,
   query_bytes := ⟨[],by decide⟩}

/-- Native range abstraction is universal over this value: no canonicality
    restriction and no rest-field dependence on its contents. -/
def product (proof semantic y1 : Slice U8) (len : 10055 ≤ proof.val.length)
    (inactive : Option LPl_Kit_Wide) : core.result.Result verifier.View verifier.Error :=
  match inactive with
  | none => .Err .Parse
  | some x => .Ok (rest proof semantic y1 len x)

/-- Exact natural-word decoder, already used in the adopted model; total on
    arbitrary bytes, including every noncanonical rejection. -/
def decoded (proof : Slice U8) : Option LPl_Kit_Wide :=
  let bs := segment proof 7495 7527
  let xs := (List.range 8).map fun i => LPn_Kit_word ((bs.val.drop (4*i)).take 4)
  if bs.val.length = 32 ∧ xs.all (fun x => x < 2147483647#u32) then
    some ⟨oldQ (LPn_Kit_q (xs.take 4)),oldQ (LPn_Kit_q (xs.drop 4))⟩ else none

theorem decoder_spec (proof : Slice U8) :
    aspis_core.field.wide_exact.WideExact.from_le_bytes (segment proof 7495 7527) =
      ok (decoded proof) := rfl

/-- Product join: inactive is DERIVED on the SAME proof bytes. No caller
    supplies an inactive value, canonicality fact, successful output or view. -/
theorem model_product (proof semantic y1 : Slice U8)
    (len : 10055 ≤ proof.val.length) :
    verifier.candidate.wide_view proof semantic y1 =
      ok (product proof semantic y1 len (decoded proof)) := by
  have s0 := range_success proof 7495 7527 (by omega)
  have s1 := range_success proof 7527 7751 (by omega)
  have s2 := range_success proof 7751 7783 (by omega)
  have s3 := range_success proof 7783 8007 (by omega)
  have s4 := range_success proof 8007 10055 (by omega)
  have size : (segment proof 7751 7783).val.length = 32 :=
    segment_length proof 7751 7783 (by omega)
  simp only [verifier.candidate.wide_view, s0, bind_tc_ok, decoder_spec]
  cases h : decoded proof with
  | none => simp only [bind_tc_ok, product]
  | some x => simp only [bind_tc_ok, s1, s2, s3, s4, dif_pos size, product, rest, root]

#print axioms range_success
#print axioms segment_length
#print axioms decoder_spec
#print axioms model_product
end LPo.View
