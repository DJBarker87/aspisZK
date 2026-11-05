import NIT_GuardComposition
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_NativeGuardJoin
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl NIT_GuardComposition
open NIT_ErrorTransport (unitReply)

def EnteredTail (c : Context) (w : Ref W) (parts : Parts) (high : RU) (out : Result NR) : Prop :=
 match high with
 | .Err _=>True
 | .Ok _=>NIT_TailChain.Trace w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress out

/-- Native SameGuard post composed with the actual tail trace on its reached
arm. An Err high reply requires no tail observation and preserves its identity. -/
theorem high (c : Context) (w : Ref W) (parts : Parts) (l : SameGuard)
 (reply guard : RU) (out : Result NR)
 (s2 : w.value.variant=FIo_Native.transport.Variant.S2) (size : c.f.value.val.length=2048)
 (ce : NHI_CellCanon.array w.value.extra)
 (hr : l.regular=unitReply (.Ok ())) (hp : l.«partial»=unitReply (.Ok ()))
 (hh : l.high=unitReply reply) (cut : cutSameGuard true l (unitReply guard))
 (tail : EnteredTail c w parts reply out) :
 dispatch guard out=afterHigh c w parts reply := by
 rw [NIT_GuardComposition.high l reply guard out hr hp hh cut]
 cases reply with
 | Err e=>rfl
 | Ok u=>
  cases u
  change out=NIT_TailChain.sourceTail _ _ _ _ _ _
  rw [NIT_TailChain.source w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress s2]
  exact (NIT_TailChain.interpreted w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress s2 size ce out tail).symm

theorem unshared (c : Context) (parts : Parts) (l : SameGuard)
 (partialReply high guard : RU) (out : Result NR)
 (domain : NIT_PairDomain.Domain c.w.value c.alpha.value c.f.value c.kappa)
 (hr : l.regular=unitReply (.Ok ())) (hp : l.«partial»=unitReply partialReply)
 (hh : l.high=unitReply high) (cut : cutSameGuard false l (unitReply guard))
 (tail : NIT_TailChain.Trace c.w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress out) :
 dispatch guard out=afterRegular c false parts (.Ok ()) := by
 rw [NIT_GuardComposition.unshared l partialReply high guard out hr hp hh cut]
 change out=NIT_TailChain.sourceTail _ _ _ _ _ _
 rw [NIT_TailChain.source c.w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress domain.s2]
 exact (NIT_TailChain.interpreted c.w c.f c.ap0 c.ap1 parts c.kappa c.lowAddress domain.s2
  (NIT_PairDomain.message_size _ _ _ _ domain) domain.extra out tail).symm

#print axioms high
#print axioms unshared
end AspisR1.NIT_NativeGuardJoin
