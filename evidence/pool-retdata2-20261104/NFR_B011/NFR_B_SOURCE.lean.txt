import NFR_RawInverseFrames
set_option autoImplicit false
noncomputable section
namespace NFR_RawInverse
open Aeneas Aeneas.Std Result WP AspisR1TerminalDecoder
open AspisR1.S2K NFO_ResultLayout

theorem accepted_bytes (bytes : Slice U8) (value : Output)
    (accepted : NFO_RawDecode.decode bytes = ok (.Ok value)) :
    (NFO_ResultLayout.bytes value).val = bytes.val := by
  have spec := NFR_RawInverseFrames.frames bytes
  rw [accepted,WP.spec_ok] at spec
  obtain ⟨width,magic,h4,h5,h6,h7,master,selected,digest,afterstate⟩ := spec value rfl
  have e4 : bytes.val[4]'(by omega) = 1#u8 := by
    have lookup : bytes.val[4]? = some (bytes.val[4]'(by omega)) := List.getElem?_eq_getElem (by omega)
    exact Option.some.inj (lookup.symm.trans h4)
  have e5 : bytes.val[5]'(by omega) = kind value.transition_kind := by
    have lookup : bytes.val[5]? = some (bytes.val[5]'(by omega)) := List.getElem?_eq_getElem (by omega)
    exact Option.some.inj (lookup.symm.trans h5)
  have e6 : bytes.val[6]'(by omega) = 1#u8 := by
    have lookup : bytes.val[6]? = some (bytes.val[6]'(by omega)) := List.getElem?_eq_getElem (by omega)
    exact Option.some.inj (lookup.symm.trans h6)
  have e7 : bytes.val[7]'(by omega) = value.output_lane := by
    have lookup : bytes.val[7]? = some (bytes.val[7]'(by omega)) := List.getElem?_eq_getElem (by omega)
    exact Option.some.inj (lookup.symm.trans h7)
  have header :
      [65#u8,83#u8,82#u8,56#u8,1#u8,kind value.transition_kind,1#u8,value.output_lane] =
      bytes.val.take 8 := by
    rw [AspisS6SliceFrame.header_eight bytes.val (by omega),magic,e4,e5,e6,e7]
    rfl
  unfold NFO_ResultLayout.bytes
  rw [stores_layout,header,master,selected,digest,afterstate]
  rw [AspisS6SliceFrame.take_append_slice bytes.val 8 40 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 40 72 (by decide),
    AspisS6SliceFrame.take_append_slice bytes.val 72 104 (by decide)]
  exact List.take_append_drop 104 bytes.val
#print axioms accepted_bytes

theorem raw_inverse : NFO_Final.RawInverse := by
  intro bytes value accepted
  apply Subtype.ext
  exact accepted_bytes (Array.to_slice bytes) value accepted
#print axioms raw_inverse

theorem accepted_codec : NFO_AcceptedAssociation.AcceptedCodec :=
  NFO_Final.codec_iff_raw.mpr raw_inverse
#print axioms accepted_codec
end NFR_RawInverse
