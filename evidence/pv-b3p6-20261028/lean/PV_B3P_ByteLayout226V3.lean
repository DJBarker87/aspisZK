import PV_B3P_BytesV3Types226
namespace PV_B3P_ByteLayout226V3
open Aeneas Aeneas.Std PV_B3P_226V3
set_option autoImplicit false
abbrev E := aspis_core.state_only_prefix.r0.Error

def wordBytes (v : U32) : List U8 :=
  [UScalar.cast .U8 v,
   UScalar.cast .U8 (U32.wrapping_shr v 8#u32),
   UScalar.cast .U8 (U32.wrapping_shr v 16#u32),
   UScalar.cast .U8 (U32.wrapping_shr v 24#u32)]

def indexBytes (v : U64) : List U8 :=
  [UScalar.cast .U8 v,
   UScalar.cast .U8 (U64.wrapping_shr v 8#u32),
   UScalar.cast .U8 (U64.wrapping_shr v 16#u32),
   UScalar.cast .U8 (U64.wrapping_shr v 24#u32),
   UScalar.cast .U8 (U64.wrapping_shr v 32#u32),
   UScalar.cast .U8 (U64.wrapping_shr v 40#u32),
   UScalar.cast .U8 (U64.wrapping_shr v 48#u32),
   UScalar.cast .U8 (U64.wrapping_shr v 56#u32)]

def fields (xs : List U32) : List U8 := xs.flatMap wordBytes

theorem fields_length (xs : List U32) : (fields xs).length = 4 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [fields, List.flatMap_cons, List.length_append, wordBytes,
      List.length_cons, List.length_nil] at *
    omega

def frontier (a : Array (Array U32 8#usize) 20#usize) : List U32 :=
  a.val.flatMap (fun x => x.val)

theorem frontier_length (a : Array (Array U32 8#usize) 20#usize) :
    (frontier a).length = 160 := by
  have h8 : (8#usize).val = 8 := by rfl
  have h20 : (20#usize).val = 20 := by rfl
  have h : ∀ xs : List (Array U32 8#usize),
      (xs.flatMap (fun x => x.val)).length = xs.length * 8 := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, Array.length_eq, List.length_cons]
      rw [ih,h8]
      omega
  unfold frontier
  rw [h, Array.length_eq,h20]

def layout (p : reference226.OwnedPublic) : List U8 :=
  [if p.withdrawal then 1#u8 else 0#u8] ++
  fields p.anchor.val ++ fields p.nullifier.val ++ fields [p.asset_id] ++
  [if p.withdrawal then 0#u8 else 1#u8] ++
  (if p.withdrawal then [] else fields p.recipient.val) ++
  fields p.change.val ++ [if p.withdrawal then 1#u8 else 0#u8] ++
  (if p.withdrawal then fields [p.withdrawal_amount] else []) ++
  indexBytes p.next_pair_index ++ fields (frontier p.frontier) ++
  fields p.next_root.val ++ fields (frontier p.next_frontier)

theorem layout_length (p : reference226.OwnedPublic) :
    (layout p).length = if p.withdrawal then 1427 else 1455 := by
  have h8 : (8#usize).val = 8 := by rfl
  cases hp : p.withdrawal <;>
    simp only [layout, hp, Bool.false_eq_true, ↓reduceIte, List.length_append,
      fields_length, Array.length_eq, h8, frontier_length, indexBytes,
      List.length_cons, List.length_nil]

-- This mathematical layout is a specification. Association to chunk/byte_at
-- and the original serializer is not assumed by these length facts.
#print axioms fields_length
#print axioms frontier_length
#print axioms layout_length
end PV_B3P_ByteLayout226V3
