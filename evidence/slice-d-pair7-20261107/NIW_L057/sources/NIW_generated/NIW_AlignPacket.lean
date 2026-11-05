import NIT_PacketTransport
import NIW_AlignRegularTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIW_AlignPacket
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl

/-- Export the supplied native-chain Result itself. Unlike packet's existence
lemma, no alternate out or alternate trace is selected. This is a helper;
the positive root must construct trace from its actual invocation. -/
theorem supplied (r : NP6_StdModel.Reservation) (w : Ref FIo_Install.W)
 (alpha : Ref (Array FE 2#usize)) (f : Ref (Slice U8)) (kappa : FE)
 (ap0 ap1 : Ref Powers) (common low scratch parts : Nat) (out : Result NR)
 (domain : NIT_PairDomain.Domain (FIo_Install.toWeights w.value)
  (NFW_PowersCohort.mapArray FIo_Install.toE alpha.value) f.value (FIo_Install.toE kappa))
 (p0 : FIo_Native.weights.powers 4#usize
  (epick (NFW_PowersCohort.mapArray FIo_Install.toE alpha.value) 0)=ok ap0.value)
 (p1 : FIo_Native.weights.powers 4#usize
  (epick (NFW_PowersCohort.mapArray FIo_Install.toE alpha.value) 1)=ok ap1.value)
 (trace : NIT_AllocatorChain.Trace
  (NIT_PacketTransport.context w alpha f kappa ap0 ap1 common low scratch parts) r out) :
 NIG_PairExport.packet r w.value alpha.value.to_slice f.value kappa=NIT_ErrorTransport.full out ∧
 NIT_ResultCanonical.Canonical out := by
 let c := NIT_PacketTransport.context w alpha f kappa ap0 ap1 common low scratch parts
 have run := NIT_AllocatorChain.interpreted r c out domain trace
 have body : (letI:=FIo_Install.allocation r
  FIo_Native.weights.Weights.pair c.w.value c.alpha.value.to_slice c.f.value c.kappa)=out := by
  letI:=FIo_Install.allocation r
  exact (NIT_PairDomain.source c.w.value c.alpha.value c.f.value
    (NIT_PairDomain.message_size _ _ _ _ domain) c.kappa).trans
   ((NIT_PairControl.source c p0 p1).trans run)
 refine ⟨?_,NIT_ResultCanonical.allocator c r out trace⟩
 rw [←NIG_PairExport.source]
 unfold FIo_Install.pair
 exact (NIT_PacketTransport.adapter _).trans (congrArg NIT_ErrorTransport.full body)

#print axioms supplied
end AspisR1.NIW_AlignPacket
