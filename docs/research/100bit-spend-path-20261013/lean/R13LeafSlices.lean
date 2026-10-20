import R13WireToBin
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.R13LeafSlices
open AspisR1Stage2 AspisR1Stage2.WireTx2 R13WireToBin

/-- WIRE-TX2 intentionally quantified over this operation. The law restores
identity of the salt bytes; width alone is insufficient. -/
def SaltLaw (ops : LeafOps) : Prop :=
  ∀ s salt, ops.salt s = ok salt → salt.val = s.val

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem range_content (q out : Slice U8) (start finish : Usize)
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
      q {start, «end» := finish} = ok out) :
    out.val = q.val.slice start.val finish.val := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeUsizeSlice,
    core.slice.index.SliceIndexRangeUsizeSlice.index] at h
  split at h
  · exact (congrArg Subtype.val (Result.ok.inj h)).symm
  · cases h

theorem prefix_content (q out : Slice U8) (finish : Usize)
    (h : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
      q {«end» := finish} = ok out) : out.val = q.val.slice 0 finish.val := by
  simp only [core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice,
    core.slice.index.SliceIndexRangeToUsizeSlice.index] at h
  split at h
  · exact (congrArg Subtype.val (Result.ok.inj h)).symm
  · cases h

/-- Source tree selector, including its actual wildcard folded-leaf branch. -/
def leafFor (tree : Usize) (q : Slice U8) : List BinMerkle32Path.Byte :=
  match tree.val with
  | 0 => BinMerkle32Leaf.c1LeafInput (bytes (q.val.slice 0 480)) (bytes (q.val.slice 608 640))
  | 1 => BinMerkle32Leaf.c2LeafInput (bytes (q.val.slice 480 608)) (bytes (q.val.slice 640 672))
  | _ => BinMerkle32Leaf.foldedLeafInput (bytes (q.val.slice 672 800)) (bytes (q.val.slice 800 832))

/-- Same packed bytes, same salt bytes, and same domain tag as the frozen
source. SaltLaw and LeafDigestLaw are the named WIRE-TX2 boundaries. -/
theorem source_leaf_exact (ops : LeafOps) (saltLaw : SaltLaw ops)
    (leafLaw : LeafDigestLaw ops)
    (c1 : ops.c1Tag = ok 113#u8) (c2 : ops.c2Tag = ok 241#u8)
    {T : Type} (D : aspis_core.digest.Digest32 T) (hash : T)
    (H : List BinMerkle32Path.Byte → BinMerkle32Path.Digest) (law : DigestLaw D hash H)
    (tree : Usize) (q : Slice U8) (out : Bytes32)
    (h : verifier.candidate.batch_leafWithWireOps ops D hash tree q = ok out) :
    digest out = H (leafFor tree q) := by
  unfold verifier.candidate.batch_leafWithWireOps at h
  unfold leafFor
  split at h <;> rename_i branch
  · obtain ⟨sb, hsb, h⟩ := bind_success _ _ _ h
    obtain ⟨salt, hs, h⟩ := bind_success _ _ _ h
    obtain ⟨packed, hp, h⟩ := bind_success _ _ _ h
    rw [c1] at h
    simp only [bind_tc_ok] at h
    rw [leafLaw D hash 113#u8 packed salt] at h
    have hd := (law _ _ h).trans (congrArg H (leaf_bytes 113#u8 packed salt))
    have hpack := prefix_content q packed 480#usize hp
    have hsalt := (saltLaw _ _ hs).trans (range_content q sb 608#usize 640#usize hsb)
    simpa only [show (480#usize).val = 480 from rfl, show (608#usize).val = 608 from rfl, show (640#usize).val = 640 from rfl, show (672#usize).val = 672 from rfl, show (800#usize).val = 800 from rfl, show (832#usize).val = 832 from rfl, branch, hpack, hsalt, show byte 113#u8 = (0x71 : BinMerkle32Path.Byte) from rfl,
      BinMerkle32Leaf.c1LeafInput] using hd
  · obtain ⟨sb, hsb, h⟩ := bind_success _ _ _ h
    obtain ⟨salt, hs, h⟩ := bind_success _ _ _ h
    obtain ⟨packed, hp, h⟩ := bind_success _ _ _ h
    rw [c2] at h
    simp only [bind_tc_ok] at h
    rw [leafLaw D hash 241#u8 packed salt] at h
    have hd := (law _ _ h).trans (congrArg H (leaf_bytes 241#u8 packed salt))
    have hpack := range_content q packed 480#usize 608#usize hp
    have hsalt := (saltLaw _ _ hs).trans (range_content q sb 640#usize 672#usize hsb)
    simpa only [show (480#usize).val = 480 from rfl, show (608#usize).val = 608 from rfl, show (640#usize).val = 640 from rfl, show (672#usize).val = 672 from rfl, show (800#usize).val = 800 from rfl, show (832#usize).val = 832 from rfl, branch, hpack, hsalt, show byte 241#u8 = (0xf1 : BinMerkle32Path.Byte) from rfl,
      BinMerkle32Leaf.c2LeafInput] using hd
  · obtain ⟨sb, hsb, h⟩ := bind_success _ _ _ h
    obtain ⟨salt, hs, h⟩ := bind_success _ _ _ h
    obtain ⟨packed, hp, h⟩ := bind_success _ _ _ h
    rw [leafLaw D hash 114#u8 packed salt] at h
    have hd := (law _ _ h).trans (congrArg H (leaf_bytes 114#u8 packed salt))
    have hpack := range_content q packed 672#usize 800#usize hp
    have hsalt := (saltLaw _ _ hs).trans (range_content q sb 800#usize 832#usize hsb)
    simpa only [show (480#usize).val = 480 from rfl, show (608#usize).val = 608 from rfl, show (640#usize).val = 640 from rfl, show (672#usize).val = 672 from rfl, show (800#usize).val = 800 from rfl, show (832#usize).val = 832 from rfl, branch, hpack, hsalt, show byte 114#u8 = (0x72 : BinMerkle32Path.Byte) from rfl,
      BinMerkle32Leaf.foldedLeafInput] using hd

#print axioms bind_success
#print axioms range_content
#print axioms prefix_content
#print axioms source_leaf_exact
end AspisR1.R13LeafSlices
