import NBL_DecodeNative
set_option autoImplicit false
noncomputable section
namespace AspisR1.NBL_SamplerNative
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open ExtractedIndexedAddSmallNatModelV1 NBL_SamplerReplay
open AspisR1GammaCaller.DigitsModel (candidateGammaHelpers)

def gammaOfRaw (v : Raw) : GammaRaw :=
  ⟨⟨⟨v.c0.c0.a,v.c0.c0.b⟩,⟨v.c0.c1.a,v.c0.c1.b⟩⟩,
    ⟨⟨v.c1.c0.a,v.c1.c0.b⟩,⟨v.c1.c1.a,v.c1.c1.b⟩⟩⟩

theorem decode_gamma (d : Digits) (canonical : Canonical d) :
    candidateGammaHelpers.decode d=ok (gammaOfRaw (NBL_DecodeNative.pack d)) := by
  change (do let raw ← AspisR1Post25Sampler.sampler.decode8 d;ok (gammaOfRaw raw))=_
  rw [NBL_DecodeNative.source d canonical,bind_tc_ok]

/-- Complete installed ordinary output on the SAME native division trace;
no decoder output or successful sampler equation is a premise. -/
theorem ordinary (block : Bytes32) (d q : Words) (tr : LowTrace block d q) :
    NBA_Installed.actual.sampling.ordinary block=
      ok (AspisR1Post25SamplerPreparedCarrier.candidateToPE (NBL_DecodeNative.pack d)) :=
  NBL_SamplerReplay.ordinary block d q tr _ (NBL_DecodeNative.source d (low block d q tr).2.1)

/-- Every arithmetic/decoder domain is derived from the same native trace. -/
theorem gamma_no_wrap (block : Bytes32) (d q d1 : Words) (n c1 : U32)
    (tr : LowTrace block d q) (nv : n.val=(quotient q).val+1)
    (first : NBA_AddCarry.Trace (values d) n.val (values d1) c1.val) (zero : c1=0#u32) :
    NBA_Installed.actual.sampling.gamma block=
      ok (AspisR1ClaimPreparedBridge.gammaToPublic (gammaOfRaw (NBL_DecodeNative.pack d1))) :=
  NBL_SamplerReplay.gamma_no_wrap block d q d1 n c1 tr nv first zero _
    (decode_gamma d1 (NBL_AddNative.canonical d n d1 c1 first))

theorem gamma_wrap (block : Bytes32) (d q d1 d2 : Words) (n c1 c2 : U32)
    (tr : LowTrace block d q) (nv : n.val=(quotient q).val+1)
    (first : NBA_AddCarry.Trace (values d) n.val (values d1) c1.val) (nonzero : c1≠0#u32)
    (second : NBA_AddCarry.Trace (values d1) 1 (values d2) c2.val) :
    NBA_Installed.actual.sampling.gamma block=
      ok (AspisR1ClaimPreparedBridge.gammaToPublic (gammaOfRaw (NBL_DecodeNative.pack d2))) :=
  NBL_SamplerReplay.gamma_wrap block d q d1 d2 n c1 c2 tr nv first nonzero second _
    (decode_gamma d2 (NBL_AddNative.canonical d1 1#u32 d2 c2 second))

#print axioms decode_gamma
#print axioms ordinary
#print axioms gamma_no_wrap
#print axioms gamma_wrap
end AspisR1.NBL_SamplerNative
end
