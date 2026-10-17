import CopyLinkWeightSource
import CopyEndpointExact

/-! Actual checked Copy link weights, from source descriptor and public index. -/
set_option autoImplicit false
namespace AspisR1.CopyLinkWeightExact
noncomputable section
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
abbrev Raw := AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.CompiledPoolV1PairForestLink
abbrev Variant := AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1
abbrev ExactQM := AspisV8R15.ExactTowerBase.QM31Exact
abbrev weightFn := AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.link_weight

def modelVariant : Variant → R0P.Variant
  | .PrivateTransfer => .privateTransfer
  | .Withdrawal => .withdrawal

def weightNat (link : Raw) (index : U64) (variant : Variant) : Nat :=
  match link.weight_kind.val with
  | 0 => 1
  | 1 => match variant with | .PrivateTransfer => 1 | .Withdrawal => 0
  | 2 => match variant with | .PrivateTransfer => 0 | .Withdrawal => 1
  | 3 => 1 - ((index.val >>> link.weight_level.val) &&& 1)
  | _ => (index.val >>> link.weight_level.val) &&& 1

private theorem kind_eq (kind : U8) (n : Nat) (hn : n < 256)
    (h : kind.val = n) : kind = @UScalar.ofNatCore .U8 n (by simpa using hn) := by
  apply UScalar.eq_of_val_eq
  simpa only [UScalar.ofNatCore_val_eq] using h

private theorem different_discriminants :
    AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.PrivateTransfer.read_discriminant ≠
    AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Withdrawal.read_discriminant := by
  change (0#isize : Isize) ≠ 1#isize
  intro he
  have hv := congrArg IScalar.val he
  have hzero : (0#isize : Isize).val = 0 := by scalar_tac
  have hone : (1#isize : Isize).val = 1 := by scalar_tac
  rw [hzero, hone] at hv
  omega

/-- The actual source weight is a canonical bit and equals the descriptor's
retained natural-number weight. Every shift, mask, cast and subtraction succeeds. -/
theorem link_weight_success (link : Raw) (index : U64) (variant : Variant)
    (hkind : link.weight_kind.val < 5) (hlevel : link.weight_level.val < 64) :
    ∃ out : field.M31, weightFn link index variant = .ok out ∧
      out.val = weightNat link index variant ∧ out.val ≤ 1 := by
  have hcases : link.weight_kind.val = 0 ∨ link.weight_kind.val = 1 ∨
      link.weight_kind.val = 2 ∨ link.weight_kind.val = 3 ∨ link.weight_kind.val = 4 := by omega
  rcases hcases with hk | hk | hk | hk | hk
  · have he : link.weight_kind = 0#u8 := kind_eq _ 0 (by omega) hk
    refine ⟨1#u32, ?_, ?_, ?_⟩
    · simp [weightFn, AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.link_weight,
        he, AspisR1CopyLinkWeightCandidate.field.M31.ONE, UScalar.ofNat, UScalar.ofNatCore]
    · simp [weightNat, hk, UScalar.ofNatCore_val_eq]
    · norm_num [UScalar.ofNatCore_val_eq]
  · have he : link.weight_kind = 1#u8 := kind_eq _ 1 (by omega) hk
    cases variant with
    | PrivateTransfer =>
      refine ⟨1#u32, ?_, ?_, ?_⟩
      · unfold weightFn AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.link_weight
        rw [he]
        simp [UScalar.ofNatCore,
          AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq,
          different_discriminants, Ne.symm different_discriminants,
          core.convert.num.FromU32Bool.from, lift, bind_tc_ok]
      · simp only [weightNat, hk]
        rfl
      · norm_num [UScalar.ofNatCore_val_eq]
    | Withdrawal =>
      refine ⟨0#u32, ?_, ?_, ?_⟩
      · unfold weightFn AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.link_weight
        rw [he]
        simp [UScalar.ofNatCore,
          AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq,
          different_discriminants, Ne.symm different_discriminants,
          core.convert.num.FromU32Bool.from, lift, bind_tc_ok]
      · simp only [weightNat, hk]
        rfl
      · norm_num [UScalar.ofNatCore_val_eq]
  · have he : link.weight_kind = 2#u8 := kind_eq _ 2 (by omega) hk
    cases variant with
    | PrivateTransfer =>
      refine ⟨0#u32, ?_, ?_, ?_⟩
      · unfold weightFn AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.link_weight
        rw [he]
        simp [UScalar.ofNatCore,
          AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq,
          different_discriminants, Ne.symm different_discriminants,
          core.convert.num.FromU32Bool.from, lift, bind_tc_ok]
      · simp only [weightNat, hk]
        rfl
      · norm_num [UScalar.ofNatCore_val_eq]
    | Withdrawal =>
      refine ⟨1#u32, ?_, ?_, ?_⟩
      · unfold weightFn AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.link_weight
        rw [he]
        simp [UScalar.ofNatCore,
          AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.Insts.CoreCmpPartialEqPoolV1PairForestCompiledVariantV1.eq,
          different_discriminants, Ne.symm different_discriminants,
          core.convert.num.FromU32Bool.from, lift, bind_tc_ok]
      · simp only [weightNat, hk]
        rfl
      · norm_num [UScalar.ofNatCore_val_eq]
  · have he : link.weight_kind = 3#u8 := kind_eq _ 3 (by omega) hk
    obtain ⟨shifted, bit, out, hs, hb, hc, hv, hbit⟩ :=
      AspisR1.CopyLinkBitArithmetic.shifted_bit_success index link.weight_level hlevel
    obtain ⟨complement, hcomplement, hvcomplement, hbound⟩ :=
      AspisR1.CopyLinkBitArithmetic.one_minus_bit_success out hbit
    refine ⟨complement, ?_, ?_, hbound⟩
    · unfold weightFn AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.link_weight
      rw [he]
      change (do
        let shifted ← index >>> link.weight_level
        let bit ← lift (shifted &&& 1#u64)
        let out ← lift (UScalar.cast .U32 bit)
        let result ← 1#u32 - out
        ok result) = .ok complement
      simp only [hs, hb, hc, hcomplement, bind_tc_ok]
    · simpa [weightNat, hk, hv] using hvcomplement
  · have he : link.weight_kind = 4#u8 := kind_eq _ 4 (by omega) hk
    obtain ⟨shifted, bit, out, hs, hb, hc, hv, hbit⟩ :=
      AspisR1.CopyLinkBitArithmetic.shifted_bit_success index link.weight_level hlevel
    refine ⟨out, ?_, ?_, hbit⟩
    · unfold weightFn AspisR1CopyLinkWeightCandidate.pool_v1.pair_forest_copy_terminal.link_weight
      rw [he]
      change (do
        let shifted ← index >>> link.weight_level
        let bit ← lift (shifted &&& 1#u64)
        let out ← lift (UScalar.cast .U32 bit)
        ok out) = .ok out
      simp only [hs, hb, hc, bind_tc_ok]
    · simpa [weightNat, hk] using hv

structure EndpointBounds (link : Raw) : Prop where
  producerRow : link.producer.row.val < 1024
  producerSlot : link.producer.slot.val < 2
  producerPattern : link.producer.pattern.val < 14
  consumerRow : link.consumer.row.val < 1024
  consumerSlot : link.consumer.slot.val < 2
  consumerPattern : link.consumer.pattern.val < 14

def modelLink (link : Raw) (hkind : link.weight_kind.val < 5)
    (hb : EndpointBounds link) : R0P.CopyLink :=
  { tag := link.tag.val,
    weightKind := ⟨link.weight_kind.val, hkind⟩,
    weightLevel := link.weight_level.val,
    producer := AspisR1.CopyEndpointExact.modelEndpoint link.producer
      hb.producerRow hb.producerSlot hb.producerPattern,
    consumer := AspisR1.CopyEndpointExact.modelEndpoint link.consumer
      hb.consumerRow hb.consumerSlot hb.consumerPattern }

theorem weightNat_model (link : Raw) (index : U64) (variant : Variant)
    (hkind : link.weight_kind.val < 5) (hb : EndpointBounds link) :
    (weightNat link index variant : ExactQM) =
      R0P.copyLinkWeight (modelLink link hkind hb) index.val (modelVariant variant) := by
  have hcases : link.weight_kind.val = 0 ∨ link.weight_kind.val = 1 ∨
      link.weight_kind.val = 2 ∨ link.weight_kind.val = 3 ∨ link.weight_kind.val = 4 := by omega
  rcases hcases with hk | hk | hk | hk | hk <;> cases variant <;>
    simp [weightNat, R0P.copyLinkWeight, modelLink, modelVariant, hk]

/-- The returned scalar is the weight of the full model link computed from
this very source descriptor; no independent model link or weight is supplied. -/
theorem link_weight_exact (link : Raw) (index : U64) (variant : Variant)
    (hkind : link.weight_kind.val < 5) (hlevel : link.weight_level.val < 64)
    (hb : EndpointBounds link) :
    ∃ out : field.M31, weightFn link index variant = .ok out ∧
      out.val ≤ 1 ∧
      (out.val : ExactQM) =
        R0P.copyLinkWeight (modelLink link hkind hb) index.val (modelVariant variant) := by
  obtain ⟨out, hr, hv, hbit⟩ := link_weight_success link index variant hkind hlevel
  refine ⟨out, hr, hbit, ?_⟩
  rw [hv]
  exact weightNat_model link index variant hkind hb

#print axioms link_weight_success
#print axioms weightNat_model
#print axioms link_weight_exact
end
end AspisR1.CopyLinkWeightExact
