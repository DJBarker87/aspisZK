import S9SharedSumObservationsV1
import S9NativeScalarTensorEmbedV1
import S9SharedCommonConstructorModelV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9SharedScalarModelValuesV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9FactorArrayEntryV1
abbrev Ctor := AspisR1S9ActualWeightsNewBoxNewV3.Weights
abbrev Table := AspisR1S9FactorTableSemanticsV1.Table
abbrev Meaning := AspisR1S9FactorTableSemanticsV1.Meaning
abbrev fromCtor := AspisR1S9FinishActualConstructorSlotV1.fromCtorWeights
abbrev ExactQM := AspisR1CurrentWide.Proof.ExactQM
abbrev E := AspisWideTower.WideExact
abbrev Row := Array (Array NativeQ 4#usize) 5#usize
abbrev Common := Array NativeQ 16#usize

def embedQ : ExactQM → E := algebraMap ExactQM E

/-- Actual source array read, with the existing exact tensor embedding. -/
theorem scalarValue_at {N : Usize} (a : Array NativeQ N) (i : Usize) (hi : i.val<N.val) :
    scalarValue a i=embedQ (AspisR1S9ActualTensorArithmeticV1.decode (atN a i hi)) := by
  unfold scalarValue
  rw [index_atN a i hi]
  exact AspisR1S9NativeScalarTensorEmbedV1.scalar_embed_tensor _

/-- The SAME completely overwritten native common buffer has the exact
constructor model's two low factors. No per-entry meaning is assumed. -/
theorem common_scalar_values_model
    (w : Ctor) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtor w))
    (selfOut : weights.Weights) (initial common : Common)
    (hloop : weights.Weights.pair_loop1 {start:=0#usize,«end»:=16#usize}
      (fromCtor w) initial=.ok (selfOut,common)) :
    selfOut=fromCtor w ∧ ∀ j : Fin 16,
      scalarValue common (finIndex (by decide) j)=
        embedQ (model 0 2 (j.val%4)*model 0 3 (j.val/4)) := by
  obtain ⟨hself,hvalues⟩ :=
    AspisR1S9SharedCommonConstructorModelV1.constructor_common_loop_success
      w model hm hc selfOut initial common hloop
  refine ⟨hself,?_⟩
  intro j
  have hj : (finIndex (by decide : 16≤64) j).val<16 := by
    simpa only [finIndex_val] using j.isLt
  obtain ⟨_,hv⟩ := hvalues (finIndex (by decide) j) hj
  rw [scalarValue_at common (finIndex (by decide) j) hj]
  apply congrArg embedQ
  simpa only [finIndex_val] using hv

/-- The SAME actual row/cell read, interpreted by the existing complete
constructor table. Every finite source index retains its exact decoded value. -/
theorem factor_scalar_values_model
    (w : Ctor) (model : Table) (hm : Meaning w.factors model)
    (k d : Usize) (hk : k.val<5) (hd : d.val<5)
    (row : Row) (coeffs : Array NativeQ 4#usize)
    (hr : Array.index_usize (fromCtor w).factors k=.ok row)
    (hc : Array.index_usize row d=.ok coeffs) :
    ∀ i : Fin 4, scalarValue coeffs (finIndex (by decide) i)=embedQ (model k.val d.val i.val) := by
  intro i
  have hi : (finIndex (by decide : 4≤64) i).val<4 := by
    simpa only [finIndex_val] using i.isLt
  let q := atN coeffs (finIndex (by decide) i) hi
  have hq := index_atN coeffs (finIndex (by decide) i) hi
  have hs := AspisR1S9ActualTensorStoredProductV1.stored_factor_read
    (fromCtor w) k d (finIndex (by decide) i) row coeffs q hr hc hq
  have ht := AspisR1S9ConstructorTableNativeTensorV1.native_stored_factor_model
    w model hm k d (finIndex (by decide) i) hk hd hi
  have hv := hs.symm.trans ht
  rw [scalarValue_at coeffs (finIndex (by decide) i) hi]
  apply congrArg embedQ
  simpa only [finIndex_val] using hv

#print axioms scalarValue_at
#print axioms common_scalar_values_model
#print axioms factor_scalar_values_model
end AspisR1S9SharedScalarModelValuesV1
