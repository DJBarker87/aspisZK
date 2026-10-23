import S9ConstructorTensorFactorMapV1
import S9FactorTableSemanticsV1
import S9ConstructorNativeReceiverCanonicalV1

set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9ConstructorTableNativeTensorV1
open AspisR1S9FactorTableSemanticsV1
abbrev CW := AspisR1S9ActualWeightsNewBoxNewV3.Weights
abbrev NQ := AspisR1S9ProductionPairCutV1.aspis_core.field.QM31
abbrev fromCtorWeights := AspisR1S9FinishActualConstructorSlotV1.fromCtorWeights
abbrev nativeDecode := AspisR1S9ActualTensorArithmeticV1.decode
abbrev highProduct := AspisR1S9ActualTensorOuterSemanticsV1.highProduct
abbrev MeaningOn := @AspisR1S9TensorIndexedMeaningV1.MeaningOn

/-- The shared complete table meaning refers to exactly the entries used by
native tensor, after the existing all-coordinate constructor carrier map. -/
theorem native_stored_factor_model
    (w : CW) (model : Table) (hm : Meaning w.factors model)
    (k d i : Usize) (hk : k.val<5) (hd : d.val<5) (hi : i.val<4) :
    AspisR1S9ActualTensorStoredProductV1.storedFactor (fromCtorWeights w) k d.val i.val =
      model k.val d.val i.val := by
  rw [AspisR1S9ConstructorTensorFactorMapV1.native_stored_factor_from_constructor]
  change rawTable w.factors k.val d.val i.val = _
  exact (rawTable_meaning w.factors k d i hk hd hi).symm.trans (hm k d i hk hd hi)

private def smallIndex (n : Nat) (hn : n<5) : Usize :=
  UScalar.ofNatCore n (by
    have hb := (5#usize).hBounds
    have h5 : (5#usize).val=5 := rfl
    rw [h5] at hb
    omega)
private theorem smallIndex_val (n : Nat) (hn : n<5) : (smallIndex n hn).val=n := by
  simp only [smallIndex,UScalar.ofNatCore_val_eq]

/-- Natural-index interface avoids expanding any of the64 tensor cells. -/
theorem native_stored_factor_model_nat
    (w : CW) (model : Table) (hm : Meaning w.factors model)
    (k : Usize) (hk : k.val<5) (d i : Nat) (hd : d<5) (hi : i<4) :
    AspisR1S9ActualTensorStoredProductV1.storedFactor (fromCtorWeights w) k d i =
      model k.val d i := by
  let dw := smallIndex d hd
  let iw := smallIndex i (by omega : i<5)
  have hdw : dw.val=d := smallIndex_val d hd
  have hiw : iw.val=i := smallIndex_val i (by omega)
  have h := native_stored_factor_model w model hm k dw iw hk
    (by rw [hdw]; exact hd) (by rw [hiw]; exact hi)
  simpa only [hdw,hiw] using h

/-- Same successful actual native tensor output has the high-factor product
of the complete constructor table. Its only compositional guards are table
meaning and native factor canonicality; the concrete constructor theorem
supplies them from that same accepted constructor execution. -/
theorem native_tensor_success_table
    (w : CW) (model : Table) (hm : Meaning w.factors model)
    (hc : AspisR1S9ConstructorNativeReceiverCanonicalV1.FactorsCanonical (fromCtorWeights w))
    (k : Usize) (hk : k.val<5) (input out : Slice NQ)
    (ht : AspisR1S9ProductionPairCutV1.weights.Weights.tensor
      (fromCtorWeights w) k 2#usize input = .ok out) :
    MeaningOn nativeDecode (highProduct (model k.val)) (fun i => i<64) out := by
  have hsource := AspisR1S9ActualTensorStoredProductV1.actual_tensor_success_stored_product
    (fromCtorWeights w) k input out (fun d row cell i q hr hcell hq => hc k d row cell i q hr hcell hq) ht
  intro i q hr hi
  have hv := hsource i q hr hi
  unfold AspisR1S9ActualTensorOuterSemanticsV1.highProduct at hv
  change nativeDecode q = model k.val 2 (i.val%4) *
    model k.val 3 ((i.val/4)%4) * model k.val 4 ((i.val/16)%4)
  rw [native_stored_factor_model_nat w model hm k hk 2 (i.val%4) (by decide) (Nat.mod_lt _ (by decide)),
    native_stored_factor_model_nat w model hm k hk 3 ((i.val/4)%4) (by decide) (Nat.mod_lt _ (by decide)),
    native_stored_factor_model_nat w model hm k hk 4 ((i.val/16)%4) (by decide) (Nat.mod_lt _ (by decide))] at hv
  exact hv

#print axioms native_stored_factor_model
#print axioms native_stored_factor_model_nat
#print axioms native_tensor_success_table
end AspisR1S9ConstructorTableNativeTensorV1
