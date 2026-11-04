import NFO_ResultLayout
import NFO_AfterstateInjective
set_option autoImplicit false
namespace NFO_ResultInjective
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder
open AspisR1.S2K NFO_ResultLayout

theorem injective (a b : Output) (same : bytes a = bytes b) : a = b := by
  have layout := congrArg (fun x : Array U8 792#usize => x.val) same
  change (ResultEncoding.stores _ _ _ _ _ _ _).val = (ResultEncoding.stores _ _ _ _ _ _ _).val at layout
  rw [stores_layout,stores_layout] at layout
  have width32 (x : Array U8 32#usize) : x.val.length=32 := x.property
  have width688 (x : Array U8 688#usize) : x.val.length=688 := x.property
  have selectedHeader := congrArg (List.take 8) layout
  have header :
      [65#u8,83#u8,82#u8,56#u8,1#u8,kind a.transition_kind,1#u8,a.output_lane] =
      [65#u8,83#u8,82#u8,56#u8,1#u8,kind b.transition_kind,1#u8,b.output_lane] := by
    simpa [List.append_assoc,List.take_append] using selectedHeader
  have kindBytes : kind a.transition_kind = kind b.transition_kind := by
    have h := congrArg (fun xs : List U8 => xs[5]?) header
    simpa using h
  have kinds : a.transition_kind = b.transition_kind := by
    cases ha : a.transition_kind <;> cases hb : b.transition_kind <;> simp_all [kind]
  have lane : a.output_lane = b.output_lane := by
    have h := congrArg (fun xs : List U8 => xs[7]?) header
    simpa using h
  have selectedMaster := congrArg (fun xs : List U8 => (xs.drop 8).take 32) layout
  have master : a.master_account = b.master_account := Subtype.ext (by
    simpa [List.append_assoc,List.drop_append,List.take_append,width32,width688] using selectedMaster)
  have selectedLane := congrArg (fun xs : List U8 => (xs.drop 40).take 32) layout
  have selected : a.selected_lane_account = b.selected_lane_account := Subtype.ext (by
    simpa [List.append_assoc,List.drop_append,List.take_append,width32,width688] using selectedLane)
  have selectedDigest := congrArg (fun xs : List U8 => (xs.drop 72).take 32) layout
  have digest : (DigestBytes.bytes a.nullifier).val = (DigestBytes.bytes b.nullifier).val := by
    simpa [List.append_assoc,List.drop_append,List.take_append,width32,width688] using selectedDigest
  rw [AspisS6NativeAfterstateEncoderReuse.native_digest_bytes,AspisS6NativeAfterstateEncoderReuse.native_digest_bytes] at digest
  have nullifier := AspisR1.JFt_DigestInjective.injective _ _ digest
  have selectedAfter := congrArg (List.drop 104) layout
  have afterBytes : AfterstateEncoding.bytes a.verified_afterstate = AfterstateEncoding.bytes b.verified_afterstate := Subtype.ext (by
    simpa [List.append_assoc,List.drop_append,width32,width688] using selectedAfter)
  have after := NFO_AfterstateInjective.injective _ _ afterBytes
  cases a
  cases b
  simp_all only
#print axioms injective
end NFO_ResultInjective
