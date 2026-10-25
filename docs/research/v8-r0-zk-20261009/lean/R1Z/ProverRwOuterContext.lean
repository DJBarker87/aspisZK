import R1Z.ProverRwOuterPrefix
import R1Z.ProverRwRngNativeBodyEmission
/-! Two concrete source operations for the public prefix, reused from the
retained actual-body extraction. This is not a native ROM/OS interpretation. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwOuterContext
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Context := aspis_core.state_only_hiding.StateOnlyHidingContext
abbrev NativeContext := ProverRwRngNativeBody.aspis_core.state_only_hiding.StateOnlyHidingContext

def toNative (c : Context) : NativeContext :=
  ⟨c.statement_digest,c.mask_nonce,c.mask_layout_fingerprint,c.layout_factor_fingerprint⟩
def fromNative (c : NativeContext) : Context :=
  ⟨c.statement_digest,c.mask_nonce,c.mask_layout_fingerprint,c.layout_factor_fingerprint⟩

theorem context_roundtrip (c : Context) : fromNative (toNative c) = c := by cases c; rfl

def construct (digest nonce : Array U8 32#usize) : Result Context := do
  let c ← ProverRwRngNativeBody.aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 digest nonce
  .ok (fromNative c)

def encode
  (self : aspis_core.state_only_hiding.StateOnlyHidingContext) :
  Result (Array Std.U8 81#usize)
  := do
  let encoded := Array.repeat 81#usize 0#u8
  let i := 1#u8
  let encoded1 ← Array.update encoded 0#usize i
  let (s, index_mut_back) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded1
      { start := 1#usize, «end» := 33#usize }
  let s1 ← lift (Array.to_slice self.statement_digest)
  let s2 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s s1
  let encoded2 := index_mut_back s2
  let (s3, index_mut_back1) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded2
      { start := 33#usize, «end» := 65#usize }
  let s4 ← lift (Array.to_slice self.mask_nonce)
  let s5 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s3 s4
  let encoded3 := index_mut_back1 s5
  let (s6, index_mut_back2) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded3
      { start := 65#usize, «end» := 73#usize }
  let a ← lift (core.num.U64.to_le_bytes self.mask_layout_fingerprint)
  let s7 ← lift (Array.to_slice a)
  let s8 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s6 s7
  let encoded4 := index_mut_back2 s8
  let (s9, index_mut_back3) ←
    core.array.Array.index_mut (core.ops.index.IndexMutSlice
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U8)) encoded4
      { start := 73#usize, «end» := 81#usize }
  let a1 ← lift (core.num.U64.to_le_bytes self.layout_factor_fingerprint)
  let s10 ← lift (Array.to_slice a1)
  let s11 ← core.slice.Slice.copy_from_slice core.marker.CopyU8 s9 s10
  ok (index_mut_back3 s11)


theorem construct_fields (digest nonce : Array U8 32#usize) :
    construct digest nonce = .ok ⟨digest,nonce,18003970557850322385#u64,7605398817818846427#u64⟩ := by
  simp only [construct,fromNative,
    ProverRwRngNativeBody.aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1,
    ProverRwRngNativeBody.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_RELATION_FREE_MASK_FINGERPRINT_V1,
    ProverRwRngNativeBody.aspis_core.state_only_hiding.PINNED_POOL_V1_PAIR_FOREST_HIDING_LAYOUT_FACTOR_FINGERPRINT_V1,
    bind_tc_ok]

/-- All other LocalLeaves fields are unused by this operation. The version
leaf is the literal existing Rust constant, not an environmental hypothesis. -/
theorem encode_source [ProverRwRngNativeBody.TypeLeaves]
    (leaves : ProverRwRngNativeBody.LocalLeaves) (c : Context) :
    encode c = @ProverRwRngNativeBody.aspis_core.state_only_hiding.StateOnlyHidingContext.encode
      _ {leaves with f11 := .ok 1#u8} (toNative c) := by rfl

variable [ExternalTypes]
@[reducible] def install (ops : ExternalFuns) : ExternalFuns :=
  {ops with op115 := construct, op116 := encode}

theorem construct_installed (ops : ExternalFuns) (digest nonce : Array U8 32#usize) :
    @aspis_core.state_only_hiding.StateOnlyHidingContext.pool_v1_pair_forest_v1 _ (install ops) digest nonce =
      construct digest nonce := by rfl

theorem encode_installed (ops : ExternalFuns) (c : Context) :
    @aspis_core.state_only_hiding.StateOnlyHidingContext.encode _ (install ops) c = encode c := by rfl

#print axioms context_roundtrip
#print axioms construct_fields
#print axioms encode_source
#print axioms construct_installed
#print axioms encode_installed
end R1Z.ProverRwOuterContext
