import AspisR1FinishDotReturnedDeltaDecodeV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1FinishDotReturnedFieldProductV1
open AspisR1FinishDotDecodedProductTrace
open AspisR1FinishDotReturnedDeltaDecodeV1
open AspisR1FinishDotReturnedProductWords AspisR1FinishRelationCurrent AspisR1FinishDotConcreteOps

abbrev M := AspisR1.R22RawQmProductResidues.M
abbrev Q := AspisV8R17.QM31WordTower.Q
abbrev ResidueQ := AspisV8R17.QM31WordResidues.Q
abbrev Wide := AspisWideTower.WideExact

def finishQMResidues (q : FinishQM) : M × M × M × M :=
  Prod.mk (q.c0.a.val : M) (Prod.mk (q.c0.b.val : M) (Prod.mk (q.c1.a.val : M) (q.c1.b.val : M)))

def finishQMResiduesQ (q : FinishQM) : ResidueQ :=
  Prod.mk (Prod.mk (q.c0.a.val : M) (q.c0.b.val : M)) (Prod.mk (q.c1.a.val : M) (q.c1.b.val : M))

def finishQMDecoded (q : FinishQM) : Q :=
  AspisV8R17.QM31WordTower.decodeQ (finishQMWords q)

def queryProductWide (x : FinishE) (q : FinishQM) : Wide :=
  ⟨finishQMDecoded x.c0 * finishQMDecoded q,
   finishQMDecoded x.c1 * finishQMDecoded q⟩

def productSum : List (Usize × FinishE × FinishQM) → Wide
  | [] => 0
  | t::xs => queryProductWide t.2.1 t.2.2 + productSum xs

theorem tupleToTowerQ_qmul (x y : AspisV8R17.QM31WordResidues.Q) :
    tupleToTowerQ (AspisR1.R22RawQmProductResidues.qmulCoefficients x y) =
      AspisV8R17.QM31WordTower.embedQ (AspisV8R17.QM31WordResidues.qMul x y) := rfl

theorem tupleToTowerQ_finishQM (q : FinishQM) :
    tupleToTowerQ (finishQMResidues q) = finishQMDecoded q := by
  simp [tupleToTowerQ, finishQMResidues, finishQMDecoded, finishQMWords,
    AspisV8R17.QM31WordTower.decodeQ, AspisV8R17.QM31WordTower.embedQ,
    AspisV8R17.QM31WordTower.embedC,
    AspisV8R17.QM31WordResidues.decodeQ,
    AspisV8R17.QM31WordResidues.decodeC]

theorem finishQM_embed_eq_decode (q : FinishQM) :
    AspisV8R17.QM31WordTower.embedQ (finishQMResiduesQ q) = finishQMDecoded q := by
  change tupleToTowerQ (finishQMResidues q) = finishQMDecoded q
  exact tupleToTowerQ_finishQM q

theorem decodeDelta_add (x y : AspisR1FinishDotDecodedProductTrace.Delta) :
    decodeDelta (deltaAdd x y) = decodeDelta x + decodeDelta y := by
  ext <;>
    simp [decodeDelta, AspisR1FinishDotDecodedProductTrace.deltaAdd,
      AspisR1EbyKPushDecodedProductUpdate.tupleAdd, tupleToTowerQ,
      AspisV8R17.QM31WordTower.embedQ, AspisV8R17.QM31WordTower.embedC]

theorem decodeDelta_query (x : FinishE) (q : FinishQM) :
    decodeDelta (queryDelta x q) = queryProductWide x q := by
  have h0 : tupleToTowerQ
      (AspisR1.R22RawQmProductResidues.qmulCoefficients
        ((x.c0.c0.a.val,x.c0.c0.b.val),(x.c0.c1.a.val,x.c0.c1.b.val))
        ((q.c0.a.val,q.c0.b.val),(q.c1.a.val,q.c1.b.val))) =
      finishQMDecoded x.c0 * finishQMDecoded q := by
    calc
      _ = AspisV8R17.QM31WordTower.embedQ
          (AspisV8R17.QM31WordResidues.qMul
            (((x.c0.c0.a.val : M),(x.c0.c0.b.val : M)),
             ((x.c0.c1.a.val : M),(x.c0.c1.b.val : M)))
            (((q.c0.a.val : M),(q.c0.b.val : M)),
             ((q.c1.a.val : M),(q.c1.b.val : M)))) := tupleToTowerQ_qmul _ _
      _ = AspisV8R17.QuadraticTowerOperations.qmul
          (AspisV8R17.QM31WordTower.embedQ (finishQMResiduesQ x.c0))
          (AspisV8R17.QM31WordTower.embedQ (finishQMResiduesQ q)) := by rfl
      _ = _ := by
        rw [AspisV8R17.QuadraticTowerOperations.qmul_eq,
          finishQM_embed_eq_decode x.c0, finishQM_embed_eq_decode q]
  have h1 : tupleToTowerQ
      (AspisR1.R22RawQmProductResidues.qmulCoefficients
        ((x.c1.c0.a.val,x.c1.c0.b.val),(x.c1.c1.a.val,x.c1.c1.b.val))
        ((q.c0.a.val,q.c0.b.val),(q.c1.a.val,q.c1.b.val))) =
      finishQMDecoded x.c1 * finishQMDecoded q := by
    calc
      _ = AspisV8R17.QM31WordTower.embedQ
          (AspisV8R17.QM31WordResidues.qMul
            (((x.c1.c0.a.val : M),(x.c1.c0.b.val : M)),
             ((x.c1.c1.a.val : M),(x.c1.c1.b.val : M)))
            (((q.c0.a.val : M),(q.c0.b.val : M)),
             ((q.c1.a.val : M),(q.c1.b.val : M)))) := tupleToTowerQ_qmul _ _
      _ = AspisV8R17.QuadraticTowerOperations.qmul
          (AspisV8R17.QM31WordTower.embedQ (finishQMResiduesQ x.c1))
          (AspisV8R17.QM31WordTower.embedQ (finishQMResiduesQ q)) := by rfl
      _ = _ := by
        rw [AspisV8R17.QuadraticTowerOperations.qmul_eq,
          finishQM_embed_eq_decode x.c1, finishQM_embed_eq_decode q]
  change (⟨tupleToTowerQ _, tupleToTowerQ _⟩ : Wide) = _
  apply QuadraticAlgebra.ext
  · exact h0
  · exact h1

theorem decodeDelta_sum (xs : List (Usize × FinishE × FinishQM)) :
    decodeDelta (deltaSum xs) = productSum xs := by
  induction xs with
  | nil =>
      simp only [AspisR1FinishDotDecodedProductTrace.deltaSum, List.map_nil,
        productSum, decodeDelta, tupleToTowerQ]
      change (0 : Wide) = 0
      rfl
  | cons t xs ih =>
      simp only [AspisR1FinishDotDecodedProductTrace.deltaSum, productSum]
      rw [decodeDelta_add, decodeDelta_query, ih]

/-- A successful source caller's returned field value is the sum of the
products represented by its successfully read weight/claim pairs. -/
theorem successful_finish_is_field_product_sum {W : Type}
    (ops : AspisR1FinishRelationCurrent.FinishOps W PushState)
    (fm : Slice U8) (ws : Slice FinishQM) (out : FinishE)
    (hrun : verifier.finish_query_dot
      (withConcreteDot (AspisR1CurrentWide.Proof.finishConcreteField ops)
        AspisR1EbyKPushDecodedProductUpdate.QRaw) fm ws = .ok (.Ok out)) :
    ∃ xs : List (Usize × FinishE × FinishQM),
      AspisR1CurrentWide.Proof.decodeFinish out = productSum xs := by
  obtain ⟨final,xs,hfinish,hdecode⟩ := successful_finish_decodes_accumulated_residues ops fm ws out hrun
  exact ⟨xs, hdecode.trans (decodeDelta_sum xs)⟩

#print axioms tupleToTowerQ_qmul
#print axioms tupleToTowerQ_finishQM
#print axioms decodeDelta_add
#print axioms decodeDelta_query
#print axioms decodeDelta_sum
#print axioms successful_finish_is_field_product_sum
end AspisR1FinishDotReturnedFieldProductV1
