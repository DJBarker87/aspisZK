import S4CanonicalBlocksV1
import R1ExactLeafFieldCodec
set_option autoImplicit false
namespace AspisR1.S4CanonicalQM31V1
open OraclePortCompactDraft AspisV8R19.DuplexFrames
open AspisR1.RetainedFieldByteCodec

theorem qm31_limb_slice (f : QM31Bytes) (limb : Fin 4) :
    List.ofFn (qm31LimbBytes f limb) = slice (List.ofFn f) (4*limb.val) 4 := by
  have hl : (slice (List.ofFn f) (4*limb.val) 4).length = 4 := by
    simp only [slice, List.length_take, List.length_drop, List.length_ofFn]
    have hb := limb.isLt
    omega
  apply List.ext_getElem (by simpa only [List.length_ofFn] using hl.symm)
  intro i hi hj
  have hi4 : i < 4 := by simpa only [List.length_ofFn] using hi
  simp only [slice, List.getElem_ofFn, List.getElem_take, List.getElem_drop]
  change f (limbByteIndex limb ⟨i, hi4⟩) = f ⟨4*limb.val+i, _⟩
  congr 1
  apply Fin.ext
  simp only [limbByteIndex_val]
  omega

theorem canonical_qm31_decode_exists (bs : Bytes) (hlen : bs.length = 16)
    (hc : canonical bs) : ∃ x, ExactLeafFieldCodec.decodeQM31 bs = some x := by
  let f : QM31Bytes := fun i => bs.get ⟨i.val, by omega⟩
  have hf : fixedBytes? 16 bs = some f := by simp [fixedBytes?, hlen, f]
  have hback : List.ofFn f = bs := ListFieldCodec.fixedBytes?_sound 16 bs f hf
  have hw : ∀ limb, (decodeWordLE (qm31LimbBytes f limb)).val < m31Modulus := by
    intro limb
    have hh := hc.2 limb.val (by simpa [hlen] using limb.isLt)
    have he : little (slice bs (4*limb.val) 4) =
        (decodeWordLE (qm31LimbBytes f limb)).val := by
      rw [← hback, ← qm31_limb_slice, MultiproofConeEndian.little_four]
    rw [he] at hh
    exact hh
  let value : QM31Limbs := fun limb => ⟨(decodeWordLE (qm31LimbBytes f limb)).val, hw limb⟩
  refine ⟨RetainedExactLimbCodec.qm31ExactLimbEquiv value, ?_⟩
  have hd : decodeQM31LE f = some value := by
    simp only [decodeQM31LE, dif_pos hw]
    rfl
  simp only [ExactLeafFieldCodec.decodeQM31, decodeQM31Bytes, hf, Option.bind_some,
    hd, Option.map_some]
#print axioms qm31_limb_slice
#print axioms canonical_qm31_decode_exists
end AspisR1.S4CanonicalQM31V1
