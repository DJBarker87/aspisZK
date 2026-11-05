import NHX_ProcessKind
import NHX_ProcessPorts
import NHX_HighReference
import NHX_KindIndex
set_option autoImplicit false
noncomputable section
namespace NHX_ProcessReference
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev Parts := Array NE 7#usize
abbrev Powers := Array NE 4#usize
abbrev Vec := alloc.vec.Vec NQ
abbrev Reply := core.result.Result Unit FIo_Native.verifier.Error
variable [FIo_Native.Allocation]

def afterBytes (kind : Usize) (scale : NE) (after : Vec) (parts : Parts)
 (r : Reply) (dot : NHM_DotPacket.Dot) : Result (Reply×Vec×Parts) := do
 let cf←core.result.Result.Insts.CoreOpsTry.branch r
 match cf with
 | core.ops.control_flow.ControlFlow.Continue _=>do
  let value←FIo_Native.fast_pairing.EbyKDot.finish dot
  let product←FIo_Native.aspis_core.field.wide_exact.WideExact.mul scale value
  let parts1←Array.update parts kind product
  ok (.Ok (),after,parts1)
 | core.ops.control_flow.ControlFlow.Break residual=>do
  let reply←core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
   Unit (core.convert.FromSame FIo_Native.verifier.Error) residual
  ok (reply,after,parts)


def reference (w : FIo_Native.weights.Weights) (kind : Usize) (f : Slice U8)
 (ap0 ap1 : Powers) (scratch : Vec) (parts : Parts) : Result (Reply×Vec×Parts) := do
 let k:=NHX_KindIndex.native kind
 let s←FIo_Native.weights.Weights.tensor w k 2#usize (alloc.vec.Vec.deref_mut scratch).1
 let row←Array.index_usize w.factors k
 let scale←NHX_HighReference.scale row ap0 ap1
 let after:=(alloc.vec.Vec.deref_mut scratch).2 s
 let initial←FIo_Native.fast_pairing.EbyKDot.new
 let payload←NHM_ByteProducts.reference f (alloc.vec.Vec.deref after) initial 64#usize
 afterBytes kind scale after parts payload.1 payload.2

/-- Same tensor, scale, dot and both Result terminals at S2/folds2/n64. -/
theorem source (w : FIo_Native.weights.Weights) (kind : Usize) (alpha : Slice NE) (f : Slice U8)
 (ap0 ap1 : Powers) (scratch : Vec) (parts : Parts) (s2:w.variant=FIo_Native.transport.Variant.S2) :
 FIo_Native.weights.process_kind w kind alpha f 2#usize 64#usize ap0 ap1 scratch parts=
 reference w kind f ap0 ap1 scratch parts := by
 rw [NHX_ProcessKind.source w kind alpha f 2#usize 64#usize ap0 ap1 scratch parts s2]
 unfold NHX_ProcessKind.reference reference afterBytes NHX_HighReference.scale
 rw [NHX_KindIndex.source]
 simp only [bind_tc_ok,ite_true,lift,bind_assoc_eq]
 rfl

#print axioms source
end NHX_ProcessReference
end
