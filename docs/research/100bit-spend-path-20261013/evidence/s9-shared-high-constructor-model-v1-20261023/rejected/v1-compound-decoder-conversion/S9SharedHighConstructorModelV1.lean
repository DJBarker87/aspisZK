import S9SharedHighScalarAssemblyV1
import S9ScalarConstructorModelV1
import S9SharedDotGuardModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9SharedHighConstructorModelV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9NativeDecodedScalarProductV1 (decodeNative)
open AspisR1S9ScalarConstructorModelV1 (factorPolynomial)
abbrev Can := AspisR1S9ActualPairWideCanonicalV1.Canonical
abbrev Parts := AspisR1S9ActualProcessKindTensorReachedV1.Parts
abbrev Powers := Array NativeW 4#usize
abbrev Common := Array NativeQ 16#usize
abbrev Partials := Array NativeW 4#usize

def rowValue (model : Table) (a0 a1 : AspisWideTower.WideExact) (f : Slice U8) (k : Nat) :=
  (factorPolynomial a0 (model k 0)*factorPolynomial a1 (model k 1))*
    ∑ i : Fin 64, fieldValue f (finIndex (by decide) i)*
      embedQ (AspisR1S9ConstructorTableNativeTensorV1.highProduct (model k) i.val)

/-- Actual shared_high writes the constructor-model point expressions into
its own output slots1/3. All scalar/dot meanings are derived from the SAME
source reads, calls and common producer. The table/receiver/powers premises
are discharged by the enclosing actual constructor and source trace. -/
theorem actual_shared_high_model_writes
    (w : Ctor) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtor w))
    (selfOut : weights.Weights) (initial common : Common)
    (hloop : weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize}
      (fromCtor w) initial=.ok (selfOut,common))
    (hguard : weights.shared_two_point_guard (fromCtor w) 2#usize=.ok true)
    (a0 a1 : NativeW) (ap0 ap1 : Powers) (ha0 : Can a0) (ha1 : Can a1)
    (hp0 : weights.powers 4#usize a0=.ok ap0)
    (hp1 : weights.powers 4#usize a1=.ok ap1)
    (f : Slice U8) (partials : Partials) (parts out : Parts)
    (hdiv : (Slice.len f /32#usize : Result Usize)=.ok (64#usize))
    (hproducer : weights.shared_partials f common=.ok (.Ok partials))
    (hparts : AspisR1S9ActualFinalSumV1.Good parts)
    (hrun : weights.shared_high partials (fromCtor w) ap0 ap1 parts=.ok (.Ok (),out)) :
    ∃ product0 product2 : NativeW,
      Can product0 ∧ Can product2 ∧
      out=(parts.set 1#usize product0).set 3#usize product2 ∧
      decodeNative product0=rowValue model (decodeNative a0) (decodeNative a1) f 0 ∧
      decodeNative product2=rowValue model (decodeNative a0) (decodeNative a1) f 2 := by
  have c0 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical a0 ap0 ha0 hp0
  have c1 := AspisR1S9ActualPairPowersProducerV1.actual_powers_four_native_reads_canonical a1 ap1 ha1 hp1
  obtain ⟨row0,row2,high0,high2,f00,f01,f20,f21,dot0,dot2,s00,s01,s20,s21,
    scale0,scale2,product0,product2,hr0,hh0,hd0,hf00,hs00,hf01,hs01,
    hr2,hh2,hd2,hf20,hs20,hf21,hs21,m00,m01,m20,m21,hscale0,hproduct0,hscale2,hproduct2,
    cp0,cp2,vp0,vp2,hout,hgood,hframe⟩ :=
    AspisR1S9SharedHighScalarAssemblyV1.shared_high_success_value_assembly
      partials (fromCtor w) ap0 ap1 parts out hc c0 c1 hparts hrun
  have d0 := AspisR1S9SharedDotConstructorModelV1.actual_shared_dot_constructor_cross_product
    w model hm hc selfOut initial common hloop 0#usize (by decide) row0 high0 hr0 hh0
    f partials dot0 hdiv hproducer hd0
  have d0' : decodeNative dot0=∑ i : Fin 64,fieldValue f (finIndex (by decide) i)*
      embedQ (AspisR1S9ConstructorTableNativeTensorV1.highProduct (model 0) i.val) := d0
  have d2 := AspisR1S9SharedDotGuardModelV1.actual_shared_row_two_dot_model
    w model hm hc selfOut initial common hloop 2#usize hguard row2 high2 hr2 hh2
    f partials dot2 hdiv hproducer hd2
  have s00v := (AspisR1S9ScalarConstructorModelV1.actual_scalar_constructor_model
    w model hm hc 0#usize 0#usize (by decide) (by decide) row0 f00 hr0 hf00 a0 ap0 s00 ha0 hp0 hs00).2
  have s01v := (AspisR1S9ScalarConstructorModelV1.actual_scalar_constructor_model
    w model hm hc 0#usize 1#usize (by decide) (by decide) row0 f01 hr0 hf01 a1 ap1 s01 ha1 hp1 hs01).2
  have s20v := (AspisR1S9ScalarConstructorModelV1.actual_scalar_constructor_model
    w model hm hc 2#usize 0#usize (by decide) (by decide) row2 f20 hr2 hf20 a0 ap0 s20 ha0 hp0 hs20).2
  have s21v := (AspisR1S9ScalarConstructorModelV1.actual_scalar_constructor_model
    w model hm hc 2#usize 1#usize (by decide) (by decide) row2 f21 hr2 hf21 a1 ap1 s21 ha1 hp1 hs21).2
  change decodeNative product0=(decodeNative s00*decodeNative s01)*decodeNative dot0 at vp0
  change decodeNative product2=(decodeNative s20*decodeNative s21)*decodeNative dot2 at vp2
  refine ⟨product0,product2,cp0,cp2,hout,?_,?_⟩
  · rw [vp0,s00v,s01v,d0']; rfl
  · rw [vp2,s20v,s21v,d2]; rfl

#print axioms actual_shared_high_model_writes
end AspisR1S9SharedHighConstructorModelV1
