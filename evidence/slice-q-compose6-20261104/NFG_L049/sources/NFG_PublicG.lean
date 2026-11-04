import NFE_NFC_CalleeDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFG_PublicG
open Aeneas Aeneas.Std Result NEV_DotCarrier
abbrev Dot := FIo_Native.fast_pairing.canonical.Dot
abbrev Acc := FIo_Native.fast_pairing.EbyKDot

abbrev Valid (scalar : NQ) : Prop := scalar.c0.a<2147483647#u32 ∧ scalar.c0.b<2147483647#u32 ∧
 scalar.c1.a<2147483647#u32 ∧ scalar.c1.b<2147483647#u32

def run (before : Acc) (scalar : NQ) (left right : Result Dot) :
 Result ((core.result.Result Unit Unit) × Acc) := do
 if before.count >= FIo_Native.fast_pairing.MAX_TERMS then ok (.Err (),before)
 else if Valid scalar then
  let first ← left
  let second ← right
  ok (.Ok (),⟨first,second,Usize.wrapping_add before.count 1#usize⟩)
 else ok (.Err (),before)

theorem check_result (scalar : NQ) :
 FIo_Native.fast_pairing.checked_q scalar=ok (if Valid scalar then .Ok (NFE_NFC_CalleeDomains.q scalar) else .Err ()) := by
 have h:=NFE_NFC_CalleeDomains.from_limbs scalar.c0.a scalar.c0.b scalar.c1.a scalar.c1.b
 simp only [FIo_Native.fast_pairing.checked_q,FIo_Native.fast_pairing.limbs_of,h,bind_tc_ok,Valid,NFE_NFC_CalleeDomains.q]
 split_ifs <;> rfl

/-- Complete native caller G after the two reached children are interpreted
on their SAME receiver fields and scalar. Rejection never evaluates a child. -/
theorem source (before : Acc) (value : NE) (scalar : NQ) :
 run before scalar
  (FIo_Native.fast_pairing.canonical.Dot.push before.c0 (NFE_NFC_CalleeDomains.q value.c0) (NFE_NFC_CalleeDomains.q scalar))
  (FIo_Native.fast_pairing.canonical.Dot.push before.c1 (NFE_NFC_CalleeDomains.q value.c1) (NFE_NFC_CalleeDomains.q scalar)) =
 FIo_Native.fast_pairing.EbyKDot.push before value scalar := by
 simp only [run,FIo_Native.fast_pairing.EbyKDot.push,NFE_NFC_CalleeDomains.from_wide,
  check_result,bind_tc_ok,Array.index_usize,Array.make]
 split_ifs <;> simp_all [core.result.Result.Insts.CoreOpsTry.branch,
  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,lift]

#print axioms check_result
#print axioms source
end AspisR1.NFG_PublicG
end
