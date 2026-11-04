import NFF_LoggedRaw
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace AspisR1.NFF_LoggedPush
open Aeneas Aeneas.Std Result

def privatePush (oracle : NFF_ProductCall.Oracle)
    (self : FIo_Native.fast_pairing.canonical.Dot) (a b : FIo_Native.fast_pairing.canonical.Q) :
    Result FIo_Native.fast_pairing.canonical.Dot := do
  let raw ← NFF_LoggedRaw.run oracle a b
  FIo_Native.fast_pairing.canonical.Dot.push_loop {start:=0#usize,«end»:=4#usize} self raw

theorem private_replay (oracle : NFF_ProductCall.Oracle) (law : NFF_ProductCall.Law oracle)
    (self : FIo_Native.fast_pairing.canonical.Dot) (a b : FIo_Native.fast_pairing.canonical.Q) :
    privatePush oracle self a b=FIo_Native.fast_pairing.canonical.Dot.push self a b := by
  simp only [privatePush,FIo_Native.fast_pairing.canonical.Dot.push,NFF_LoggedRaw.headline oracle law]

def publicPush
  (oracle : NFF_ProductCall.Oracle)
  (self : FIo_Native.fast_pairing.EbyKDot) (value : FIo_Native.aspis_core.field.wide_exact.WideExact)
  (scalar : FIo_Native.aspis_core.field.QM31) :
  Result ((core.result.Result Unit Unit) × FIo_Native.fast_pairing.EbyKDot)
  := do
  if self.count >= FIo_Native.fast_pairing.MAX_TERMS
  then ok (core.result.Result.Err (), self)
  else
    let a ← FIo_Native.fast_pairing.canonical.Q.from_wide value
    let value_c0 ← Array.index_usize a 0#usize
    let value_c1 ← Array.index_usize a 1#usize
    let r ← FIo_Native.fast_pairing.checked_q scalar
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let d ← privatePush oracle self.c0 value_c0 val
      let d1 ← privatePush oracle self.c1 value_c1 val
      let i ← lift (Std.Usize.wrapping_add self.count 1#usize)
      ok (core.result.Result.Ok (), { c0 := d, c1 := d1, count := i })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame Unit) residual
      ok (r1, self)


theorem public_replay (oracle : NFF_ProductCall.Oracle) (law : NFF_ProductCall.Law oracle)
    (self : FIo_Native.fast_pairing.EbyKDot) (value : NEV_DotCarrier.NE) (scalar : NEV_DotCarrier.NQ) :
    publicPush oracle self value scalar=FIo_Native.fast_pairing.EbyKDot.push self value scalar := by
  simp only [publicPush,FIo_Native.fast_pairing.EbyKDot.push,private_replay oracle law]
  rfl

#print axioms private_replay
#print axioms public_replay
end AspisR1.NFF_LoggedPush
end
