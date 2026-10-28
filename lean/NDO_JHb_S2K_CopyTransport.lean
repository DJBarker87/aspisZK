import NDO_JHb_S2K_TrustedStd

/-! Exact width32 primitive join. Native validity/region interpretation is an
explicit runtime admission; this theorem supplies no enclosing caller success. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1.S2K.CopyTransport

theorem range32 {Frame : Type}
    (copy : List U8 → List U8 → Frame → StdCopy.Outcome Frame)
    (std : StdCopy.TrustedStd copy) (frame : Frame)
    (output : Array U8 688#usize) (start stop : Usize) (bytes : Array U8 32#usize)
    (order : start.val ≤ stop.val) (bound : stop.val ≤ 688)
    (width : stop.val - start.val = 32) :
    copy ((output.val.drop start.val).take 32) bytes.val frame =
      .returned bytes.val frame ∧
    SourceStore.store output start stop bytes =
      ok (output.setSlice! start.val bytes.val) := by
  constructor
  · apply StdCopy.equal_lengths copy std
    have room : 32 ≤ 688-start.val := by omega
    simp only [List.length_take,List.length_drop,output.property,bytes.property]
    exact Nat.min_eq_left room
  · exact SourceStore.store_exact output start stop bytes order bound width

#print axioms range32
end AspisR1.S2K.CopyTransport
