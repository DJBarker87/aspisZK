import R1Z.PV_CB_Op84Funs
import R1Z.PV_RE_NoCatchCore
set_option autoImplicit false
namespace R1Z.PV_RE_Op84Forward6
open Aeneas Aeneas.Std Result
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
def frame (tag : U8) (values : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 2#usize
    [Array.to_slice (Array.make 2#usize [16#u8,tag]),values])

/-- The exact extracted leaf invokes the supplied callback on this frame.
There is no Result matcher between this invocation and its returned Result. -/
theorem invocation (hash : Hash) (tag : U8) (values : Slice U8) :
    PV_CB_ShippedOp84Fresh.aspis_core.r0.merkle.leaf hash tag values =
      hash (frame tag values) := by
  rfl

theorem noCatch (tag : U8) (values : Slice U8) :
    PV_RE_NoCatchCore.NoCatch (fun pending : Result (Array U8 32#usize) =>
      PV_CB_ShippedOp84Fresh.aspis_core.r0.merkle.leaf
        (fun _ => pending) tag values) := by
  constructor
  · intro e; rfl
  · rfl

theorem failure (hash : Hash) (tag : U8) (values : Slice U8) (e : Error)
    (h : hash (frame tag values) = .fail e) :
    PV_CB_ShippedOp84Fresh.aspis_core.r0.merkle.leaf hash tag values = .fail e := by
  rw [invocation, h]

theorem divergence (hash : Hash) (tag : U8) (values : Slice U8)
    (h : hash (frame tag values) = .div) :
    PV_CB_ShippedOp84Fresh.aspis_core.r0.merkle.leaf hash tag values = .div := by
  rw [invocation, h]
#print axioms frame
#print axioms invocation
#print axioms noCatch
#print axioms failure
#print axioms divergence
end R1Z.PV_RE_Op84Forward6
