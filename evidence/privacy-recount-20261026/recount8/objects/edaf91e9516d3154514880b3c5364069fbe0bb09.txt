-- Generated definitions retained from aeneas-source-op246-003; carrier alias only.
import R1Z.ProverRwSuccessHashes
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PV_CB3_ShippedOp246
abbrev aspis_core.digest.Digest32 := ProverRwFull.aspis_core.digest.Digest32

/-- [pv_cb3_source::multiproof::BINARY_NODE_TAG]
    Source: '../source/crates/aspis-r1-cost-probe/src/multiproof.rs', lines 21:0-21:37
    Visibility: public -/
@[global_simps, irreducible] def multiproof.BINARY_NODE_TAG : Std.U8 := 18#u8

/-- [pv_cb3_source::multiproof::binary_parent]:
    Source: '../source/crates/aspis-r1-cost-probe/src/multiproof.rs', lines 49:0-51:1
    Visibility: public -/
def multiproof.binary_parent
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (left : Array Std.U8 32#usize) (right : Array Std.U8 32#usize) :
  Result (Array Std.U8 32#usize)
  := do
  let s ←
    lift (Array.to_slice (Array.make 1#usize [ multiproof.BINARY_NODE_TAG ]))
  let s1 ← lift (Array.to_slice left)
  let s2 ← lift (Array.to_slice right)
  let s3 ← lift (Array.to_slice (Array.make 3#usize [ s, s1, s2 ]))
  aspis_coredigestDigest32Inst.digest hash s3

/-- [pv_cb3_source::binary_parent]:
    Source: 'lib.rs', lines 17:0-19:1
    Visibility: public -/
def binary_parent
  {H : Type} (aspis_coredigestDigest32Inst : aspis_core.digest.Digest32 H)
  (hash : H) (left : Array Std.U8 32#usize) (right : Array Std.U8 32#usize) :
  Result (Array Std.U8 32#usize)
  := do
  multiproof.binary_parent aspis_coredigestDigest32Inst hash left right

end PV_CB3_ShippedOp246

namespace R1Z.PV_CB3_Op246Source
open Aeneas Aeneas.Std Result ProverRwFull
set_option autoImplicit false
noncomputable section
variable [ExternalTypes]
/-- Complete arbitrary-callback Result equation, including failure and divergence. -/
theorem op246_source (ops : ExternalFuns) {H : Type}
    (inst : aspis_core.digest.Digest32 H) (hash : H)
    (left right : Array U8 32#usize) :
    (ProverRwSuccessHashes.selected ops).op246 inst hash left right =
      PV_CB3_ShippedOp246.multiproof.binary_parent inst hash left right := by
  unfold PV_CB3_ShippedOp246.multiproof.binary_parent
    PV_CB3_ShippedOp246.multiproof.BINARY_NODE_TAG
  rfl
#print axioms op246_source
end
end R1Z.PV_CB3_Op246Source
