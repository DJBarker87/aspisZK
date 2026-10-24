import S9SharedHighConstructorModelV1
import S9TwoFoldProductModelV1
import S9SymbolicRowTransportV1
import S9SourceFactorShapeTransportV1
import S9SourceQuarterModelBridgeV1
import S9OpaqueQEmbedTripleV1
import S9PointOperatorTransportV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open scoped BigOperators
namespace AspisR1S9PointRowDualFoldModelV1
open AspisR1
open AspisR1S9SharedScalarModelValuesV1
open AspisR1S9SharedSumObservationsV1
open AspisR1S9SharedHighConstructorModelV1 (rowValue)
open AspisR1S9ScalarConstructorModelV1 (factorPolynomial)
abbrev E := AspisWideTower.WideExact
abbrev highProduct := AspisR1S9ConstructorTableNativeTensorV1.highProduct

/-- The five radix-four factors of ONE constructor table row. This is a
model expression; correspondence to a public functional is supplied by the
complete same-constructor statement/circle semantics. -/
def rawRow (model : Table) (k : Nat) (j : Fin 1024) : ExactQM :=
  model k 0 (j.val%4)*model k 1 ((j.val/4)%4)*highProduct (model k) (j.val/16)

theorem rawRow_children (model : Table) (k : Nat) (d : Fin 64) (t1 t0 : Fin 4) :
    rawRow model k (childIndex (childIndex d t1) t0)=
      model k 0 t0.val*model k 1 t1.val*highProduct (model k) d.val := by
  unfold rawRow
  simp only [childIndex_val]
  have h0 : (4*(4*d.val+t1.val)+t0.val)%4=t0.val := by
    have := t0.isLt; have := t1.isLt; omega
  have h1 : ((4*(4*d.val+t1.val)+t0.val)/4)%4=t1.val := by
    have := t0.isLt; have := t1.isLt; omega
  have h2 : (4*(4*d.val+t1.val)+t0.val)/16=d.val := by
    have := t0.isLt; have := t1.isLt; omega
  rw [h0,h1,h2]

theorem factor_model_eq (alpha : E) (a : Nat → ExactQM) :
    AspisR1S9TwoFoldProductModelV1.factor alpha (fun t : Fin 4 => embedQ (a t.val))=
      factorPolynomial alpha a := by
  have hl := AspisR1S9SymbolicRowTransportV1.factor_shape alpha
    (fun t : Fin 4 => embedQ (a t.val))
  have hq : (RoundPairing.quarter : E)=AspisR1S9ScalarActualPowerPolynomialV1.quarter :=
    AspisR1S9SourceQuarterModelBridgeV1.source_quarter_eq_model_quarter.symm
  have hc := AspisR1S9SymbolicRowTransportV1.shape_quarter_congr alpha
    (fun t : Fin 4 => embedQ (a t.val)) RoundPairing.quarter
    AspisR1S9ScalarActualPowerPolynomialV1.quarter hq
  exact hl.trans (hc.trans (AspisR1S9SourceFactorShapeTransportV1.source_factor_eq_generic_shape alpha a).symm)

theorem embedded_raw_children (model : Table) (k : Nat) (d : Fin 64) (t1 t0 : Fin 4) :
    embedQ (rawRow model k (childIndex (childIndex d t1) t0))=
      (embedQ (model k 0 t0.val)*embedQ (model k 1 t1.val))*
        embedQ (highProduct (model k) d.val) := by
  have hr := congrArg embedQ (rawRow_children model k d t1 t0)
  have hm := AspisR1S9OpaqueQEmbedTripleV1.embedQ_triple
    (model k 0 t0.val) (model k 1 t1.val) (highProduct (model k) d.val)
  exact hr.trans hm

/-- Two model dual folds of the row are exactly the source scalar factors
and its remaining high product. Existing four-child Horner algebra is reused;
no 1024-cell concrete expansion is evaluated. -/
theorem point_row_two_dual_folds (model : Table) (k : Nat) (a0 a1 : E) (d : Fin 64) :
    RoundPairing.dualFold a1
      (RoundPairing.dualFold a0 (fun j => embedQ (rawRow model k j))) d=
      (factorPolynomial a0 (model k 0)*factorPolynomial a1 (model k 1))*
        embedQ (highProduct (model k) d.val) := by
  have hh := AspisR1S9TwoFoldProductModelV1.two_dual_fold_child_product
    a0 a1 (fun j => embedQ (rawRow model k j))
    (fun t : Fin 4 => embedQ (model k 0 t.val))
    (fun t : Fin 4 => embedQ (model k 1 t.val))
    (fun d : Fin 64 => embedQ (highProduct (model k) d.val)) d
    (fun t1 t0 => (embedded_raw_children model k d t1 t0).trans
      (AspisR1S9PointOperatorTransportV1.triple_operator_eq
        (embedQ (model k 0 t0.val)) (embedQ (model k 1 t1.val))
        (embedQ (highProduct (model k) d.val))))
  have he := congrArg₂ (fun x y : E => x*y)
    (factor_model_eq a0 (model k 0)) (factor_model_eq a1 (model k 1))
  have ht := AspisR1S9PointOperatorTransportV1.triple_operator_eq
    (AspisR1S9TwoFoldProductModelV1.factor a0 (fun t : Fin 4 => embedQ (model k 0 t.val)))
    (AspisR1S9TwoFoldProductModelV1.factor a1 (fun t : Fin 4 => embedQ (model k 1 t.val)))
    (embedQ (highProduct (model k) d.val))
  exact (hh.trans ht.symm).trans
    (congrArg (fun z : E => z*embedQ (highProduct (model k) d.val)) he)

/-- The actual source-buffer field observation vector is kept fixed. Its
constructor-model rowValue equals the model's precise two-fold dual dot.
This transports the optimized point-part expression, not an independently
chosen coefficient/input vector. -/
theorem rowValue_eq_two_dual_dot (model : Table) (k : Nat) (a0 a1 : E) (f : Slice U8) :
    rowValue model a0 a1 f k=
      RoundPairing.dot (fun i : Fin 64 => fieldValue f (finIndex (by decide) i))
        (RoundPairing.dualFold a1
          (RoundPairing.dualFold a0 (fun j => embedQ (rawRow model k j)))) := by
  have hd := AspisR1S9SymbolicRowTransportV1.dot_scaled_transport
    (fun i : Fin 64 => fieldValue f (finIndex (by decide) i))
    (fun i : Fin 64 => embedQ (highProduct (model k) i.val))
    (RoundPairing.dualFold a1
      (RoundPairing.dualFold a0 (fun j => embedQ (rawRow model k j))))
    (factorPolynomial a0 (model k 0)*factorPolynomial a1 (model k 1))
    (fun i => (point_row_two_dual_folds model k a0 a1 i).trans
      (AspisR1S9WideMulOperatorBridgeV1.mul_operator_eq _ _))
  have hs := AspisR1S9PointOperatorTransportV1.scaled_sum_operator_eq
    (factorPolynomial a0 (model k 0)*factorPolynomial a1 (model k 1))
    (fun i : Fin 64 => fieldValue f (finIndex (by decide) i))
    (fun i : Fin 64 => embedQ (highProduct (model k) i.val))
  exact hs.trans hd.symm

#print axioms rawRow_children
#print axioms factor_model_eq
#print axioms point_row_two_dual_folds
#print axioms rowValue_eq_two_dual_dot
end AspisR1S9PointRowDualFoldModelV1
