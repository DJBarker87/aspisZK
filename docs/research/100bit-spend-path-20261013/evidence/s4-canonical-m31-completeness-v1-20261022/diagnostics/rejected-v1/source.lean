import S4CanonicalBlocksV1
import R1ExactLeafFieldCodec
set_option autoImplicit false
namespace AspisR1.S4CanonicalM31V1
open OraclePortCompactDraft AspisV8R19.DuplexFrames
open AspisR1.RetainedFieldByteCodec

theorem canonical_m31_decode_exists (bs : Bytes) (hlen : bs.length = 4)
    (hc : canonical bs) : ∃ x, ExactLeafFieldCodec.decodeM31 bs = some x := by
  let f : WordBytes := fun i => bs.get ⟨i.val, by omega⟩
  have hf : fixedBytes? 4 bs = some f := by simp [fixedBytes?, hlen, f]
  have hback : List.ofFn f = bs := ListFieldCodec.fixedBytes?_sound 4 bs f hf
  have hfirst : little bs < 2147483647 := by
    have hh := hc.2 0 (by simp [hlen])
    simpa [slice, List.take_of_length_le (by omega : bs.length ≤ 4)] using hh
  have hw : (decodeWordLE f).val < m31Modulus := by
    have he := MultiproofConeEndian.little_four f
    rw [hback] at he
    rw [← he]
    exact hfirst
  let value : M31Value := ⟨(decodeWordLE f).val, hw⟩
  refine ⟨RetainedExactLimbCodec.m31ResidueEquiv value, ?_⟩
  have hd : decodeM31LE f = some value := by
    simp only [decodeM31LE, dif_pos hw]
  simp only [ExactLeafFieldCodec.decodeM31, decodeM31Bytes, hf, Option.bind_some, hd,
    Option.map_some]
#print axioms canonical_m31_decode_exists
end AspisR1.S4CanonicalM31V1
