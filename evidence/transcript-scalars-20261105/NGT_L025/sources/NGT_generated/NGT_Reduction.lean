import NGT_NBL_SamplerNative
import NGT_NBL_SamplerDebug
import NGT_NBA_Rho
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGT_Reduction
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open NGT_NBL_SamplerReplay

/-- Local native arithmetic observations, not a whole sampler equality. Native
steps and the retained LPk/NBL inductions construct these on the same bytes. -/
inductive Scalar (block : Bytes32) : Bool → aspis_core.field.WideExact → Prop where
 | ordinary (d q : Words) (low : LowTrace block d q) :
   Scalar block false (AspisR1Post25SamplerPreparedCarrier.candidateToPE (NGT_NBL_DecodeNative.pack d))
 | plain (d q d1 : Words) (n c : U32) (low : LowTrace block d q)
   (increment : n.val=(quotient q).val+1)
   (add : NBA_AddCarry.Trace (ExtractedIndexedAddSmallNatModelV1.values d) n.val
     (ExtractedIndexedAddSmallNatModelV1.values d1) c.val) (zero : c=0#u32) :
   Scalar block true (AspisR1ClaimPreparedBridge.gammaToPublic
     (NGT_NBL_SamplerNative.gammaOfRaw (NGT_NBL_DecodeNative.pack d1)))
 | wrapped (d q d1 d2 : Words) (n c1 c2 : U32) (low : LowTrace block d q)
   (increment : n.val=(quotient q).val+1)
   (first : NBA_AddCarry.Trace (ExtractedIndexedAddSmallNatModelV1.values d) n.val
     (ExtractedIndexedAddSmallNatModelV1.values d1) c1.val) (nonzero : c1≠0#u32)
   (second : NBA_AddCarry.Trace (ExtractedIndexedAddSmallNatModelV1.values d1) 1
     (ExtractedIndexedAddSmallNatModelV1.values d2) c2.val) :
   Scalar block true (AspisR1ClaimPreparedBridge.gammaToPublic
     (NGT_NBL_SamplerNative.gammaOfRaw (NGT_NBL_DecodeNative.pack d2)))

theorem scalar {block : Bytes32} {mode : Bool} {out : aspis_core.field.WideExact}
 (native : Scalar block mode out) :
 (if mode then NGT_NBA_Installed.actual.sampling.gamma block else
   NGT_NBA_Installed.actual.sampling.ordinary block)=ok out := by
 cases native with
 | ordinary d q low => exact NGT_NBL_SamplerNative.ordinary block d q low
 | plain d q d1 n c low increment add zero =>
   exact NGT_NBL_SamplerNative.gamma_no_wrap block d q d1 n c low increment add zero
 | wrapped d q d1 d2 n c1 c2 low increment first nonzero second =>
   exact NGT_NBL_SamplerNative.gamma_wrap block d q d1 d2 n c1 c2 low increment first nonzero second

/-- The second-add stub's false carry is derived on its actual reached domain. -/
theorem second_carry (block : Bytes32) (d q d1 d2 : Words) (n c1 c2 : U32)
 (low : LowTrace block d q) (increment : n.val=(quotient q).val+1)
 (first : NBA_AddCarry.Trace (ExtractedIndexedAddSmallNatModelV1.values d) n.val
   (ExtractedIndexedAddSmallNatModelV1.values d1) c1.val) (nonzero : c1≠0#u32)
 (second : NBA_AddCarry.Trace (ExtractedIndexedAddSmallNatModelV1.values d1) 1
   (ExtractedIndexedAddSmallNatModelV1.values d2) c2.val) : c2=0#u32 :=
 NGT_NBL_SamplerDebug.source block d q d1 d2 n c1 c2 low increment first nonzero second

/-- Four native long-division passes, followed by the exact four returned
coordinates. No desired sampler Result is a field of this certificate. -/
structure K (block : Bytes32) (out : aspis_core.field.QM31) where
 digits : List Nat
 last : List UInt32
 division : LPk_Induction.Digits 4 (SamplerBytePass.digits block) digits last
 packing : NGT_NBA_Rho.coordinates out=digits

theorem scalar_k {block : Bytes32} {out : aspis_core.field.QM31}
 (native : K block out) : AspisR1PublicPreparation.sampler.qm31_sample block=ok out :=
 NGT_NBA_Rho.source block native.digits native.last out native.division native.packing
#print axioms scalar
#print axioms second_carry
#print axioms scalar_k
end AspisR1.NGT_Reduction
