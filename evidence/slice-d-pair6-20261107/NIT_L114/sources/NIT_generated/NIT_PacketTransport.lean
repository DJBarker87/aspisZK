import NIT_PairComposition
import NIT_ResultCanonical
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIT_PacketTransport
open Aeneas Aeneas.Std Result LPi_FieldValues NIT_Cuts NIT_PairControl AspisR1Stage2

def context (w : Ref FIo_Install.W) (alpha : Ref (Array FE 2#usize))
 (f : Ref (Slice U8)) (kappa : FE) (ap0 ap1 : Ref Powers)
 (common low scratch parts : Nat) : Context :=
 ⟨⟨w.address,FIo_Install.toWeights w.value⟩,
 ⟨alpha.address,NFW_PowersCohort.mapArray FIo_Install.toE alpha.value⟩,
 f,ap0,ap1,FIo_Install.toE kappa,common,low,scratch,parts⟩

/-- Lossless adapter for a complete result, including all verifier errors and
outer fail/div. This is the actual installed coordinate adapter. -/
theorem adapter (out : Result NR) :
 (do let reply←out
     match reply with
     | .Ok x=>ok (.Ok (FIo_Install.fromE x))
     | .Err e=>ok (.Err (FIo_Install.error e)))=NIT_ErrorTransport.full out := by
 cases out with
 | fail e=>rfl
 | div=>rfl
 | ok reply=>cases reply <;> rfl

/-- Exact exported model packet on SAME caller inputs, with a constructed
Initial cut and all loop traces. This does not assert a native whole-pair
execution certificate; no such endpoint equality is supplied as a premise. -/
theorem packet (r : NP6_StdModel.Reservation) (w : Ref FIo_Install.W)
 (alpha : Ref (Array FE 2#usize)) (f : Ref (Slice U8)) (kappa : FE)
 (ap0Address ap1Address common low scratch parts : Nat)
 (domain : NIT_PairDomain.Domain (FIo_Install.toWeights w.value)
  (NFW_PowersCohort.mapArray FIo_Install.toE alpha.value) f.value (FIo_Install.toE kappa)) :
 ∃ (ap0 ap1 : Powers) (l : Initial) (out : Result NR),
 cutInitial (NFW_PowersCohort.mapArray FIo_Install.toE alpha.value) l ap0 ap1 initial ∧
 NIT_AllocatorChain.Trace (context w alpha f kappa ⟨ap0Address,ap0⟩ ⟨ap1Address,ap1⟩ common low scratch parts) r out ∧
 NIG_PairExport.packet r w.value alpha.value.to_slice f.value kappa=NIT_ErrorTransport.full out ∧
 NIT_ResultCanonical.Canonical out := by
 obtain ⟨ap0,ap1,l,cut,p0,p1,c0,c1⟩ := NIT_PairComposition.initial_exists _ domain.alphas
 let c:=context w alpha f kappa ⟨ap0Address,ap0⟩ ⟨ap1Address,ap1⟩ common low scratch parts
 obtain ⟨out,trace,source⟩ := NIT_PairComposition.full_model_chain r c domain p0 p1 c0 c1
 refine ⟨ap0,ap1,l,out,cut,trace,?_,NIT_ResultCanonical.allocator c r out trace⟩
 rw [←NIG_PairExport.source]
 unfold FIo_Install.pair
 change (do let reply←@FIo_Native.weights.Weights.pair (FIo_Install.allocation r)
          c.w.value c.alpha.value.to_slice c.f.value c.kappa
            match reply with
            | .Ok x=>ok (.Ok (FIo_Install.fromE x))
            | .Err e=>ok (.Err (FIo_Install.error e)))=NIT_ErrorTransport.full out
 rw [source]
 exact adapter out

#print axioms adapter
#print axioms packet
end AspisR1.NIT_PacketTransport
