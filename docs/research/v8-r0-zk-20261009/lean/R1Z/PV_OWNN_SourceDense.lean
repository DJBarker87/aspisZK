import R1Z.PV_OWNM_V239
import R1Z.PV_OWNM_DenseRows
import R1Z.PV_OWNM_FoldSum
import R1Z.PV_OWNL_Suffix
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNN_SourceDense
open scoped BigOperators
open Aeneas Aeneas.Std Result PV_OWNI_RawOps PV_OWNI_Scanner
open PV_OWNI_DensePrune PV_OWNL_RowEnumeration
variable {K : Type} [Field K]

theorem take_coordinates (decode : Q → K) (point : List Q) (w : Nat)
 (hw : w ≤ point.length) :
 (point.take w).map decode = List.ofFn (fun i : Fin w => decode (point[i.val]?.getD zero)) := by
 apply List.ext_getElem
 · simp only [List.length_map,List.length_take,List.length_ofFn,Nat.min_eq_left hw]
 · intro i hi hj
   have hb : i < point.length := by
    have hn : i<w := by simpa only [List.length_ofFn] using hj
    omega
   simp only [List.getElem_map,List.getElem_take,List.getElem_ofFn,
    List.getElem?_eq_getElem hb,Option.getD_some]

theorem prefix_weight (decode : Q → K) (D : PV_OWNJ_DecodeFold.Decoder decode)
 (point : List Q) (w : Nat) (hw : w ≤ point.length) (a : Fin (2^w))
 (hp : ∀ q ∈ point, PV_OWNJ_DecodeFold.Canon q) :
 decode (((point.take w).foldl (PV_OWNI_WeightTotal.step w a.val) (ops.one,0)).1) =
 weight (fun i : Fin w => decode (point[i.val]?.getD zero)) (tail w a) := by
 rw [one_value]
 have h := PV_OWNJ_DecodeWeight.weight decode D w a.val (point.take w) (one,0)
  D.one_canon (fun q hq => hp q (List.mem_of_mem_take hq))
 have hh := congrArg (fun x : K × Nat => x.1) h.2
 simp only [D.one_eq] at hh
 rw [hh,take_coordinates decode point w hw]
 change ((List.ofFn (fun i : Fin w => decode (point[i.val]?.getD zero))).foldl
  (PV_OWNL_PrefixProduct.step w a.val) (1,0)).1 = _
 have hprod := PV_OWNL_PrefixProduct.prefix_weight
  (List.ofFn (fun i : Fin w => decode (point[i.val]?.getD zero)))
  (⟨a.val,by simpa only [List.length_ofFn] using a.isLt⟩)
 simp only [List.length_ofFn,weight,tail,List.get_eq_getElem,List.getElem_ofFn] at hprod
 exact hprod.trans (Fin.prod_congr'
  (fun i : Fin w => if a.val.testBit (w-1-i.val) then decode (point[i.val]?.getD zero)
   else 1-decode (point[i.val]?.getD zero))
  (show (List.ofFn (fun i : Fin w => decode (point[i.val]?.getD zero))).length = w
   from List.length_ofFn))

/-- The scanner partitions the point into its non-Boolean prefix and Boolean suffix. -/
theorem scanner_suffix_length (point : List Q) :
 (point.drop (width point)).length = trailing point := by
 have hs := PV_RDB2D_SparseShape.split_length boolean point
 have hw : width point ≤ point.length := by
  unfold width PV_RDB2D_SparseShape.prefixLen
  omega
 simp only [List.length_drop]
 change width point + trailing point = point.length at hs
 omega

/-- Transport the suffix index before applying the dependent scanner theorem. -/
theorem scanner_decoded_cast (decode : Q → K)
 (D : PV_OWNJ_DecodeFold.Decoder decode) (point : List Q)
 (i : Fin (trailing point)) :
 decode ((point.drop (width point)).get
  (Fin.cast (scanner_suffix_length point).symm i)) =
 if (suffix point).testBit (trailing point-1-i.val) then 1 else 0 := by
 have h := PV_OWNL_Suffix.scanner_decoded decode D.zero_eq D.one_eq point
  (Fin.cast (scanner_suffix_length point).symm i)
 exact h.trans (congrArg (fun n => if (suffix point).testBit (n-1-i.val)
   then (1 : K) else 0) (scanner_suffix_length point))

theorem sparse_dense (decode : Q → K) (D : PV_OWNJ_DecodeFold.Decoder decode)
 (point column : List Q) (hl : point.length=10)
 (hp : ∀ q ∈ point, PV_OWNJ_DecodeFold.Canon q) :
 PV_OWNJ_ValueBridge.sparse decode point column = PV_OWNM_V239.dense decode zero point column := by
 let w := width point
 let t := trailing point
 have split : w+t=10 := PV_OWNI_Scanner.split point hl
 have hw : w ≤ point.length := by omega
 have htlen : (point.drop w).length = t := scanner_suffix_length point
 let suffix : Fin (2^t) := ⟨PV_OWNI_Scanner.suffix point,suffix_bound point⟩
 have hs : ∀ i : Fin t,
  decode (point[(Fin.natAdd w i).val]?.getD zero) = if tail t suffix i then 1 else 0 := by
  intro i
  have hd := scanner_decoded_cast decode D point i
  have hb : w+i.val < point.length := by omega
  simpa only [List.get_eq_getElem, List.getElem_drop, Fin.val_cast,
   Fin.val_natAdd, List.getElem?_eq_getElem hb, Option.getD_some, tail, suffix] using hd
 have hd := PV_OWNM_DenseRows.full_dense_sparse w t
  (fun i : Fin (w+t) => decode (point[i.val]?.getD zero)) suffix
  (fun r : Fin (2^(w+t)) => decode (column[r.val]?.getD zero)) hs
 have hf : PV_OWNM_DenseRows.fullDense (w+t)
  (fun i : Fin (w+t) => decode (point[i.val]?.getD zero))
  (fun r : Fin (2^(w+t)) => decode (column[r.val]?.getD zero)) =
  PV_OWNM_V239.dense decode zero point column := by
  rw [split]
  rfl
 rw [hf] at hd
 rw [hd,PV_OWNM_FoldSum.sparse_sum]
 apply Finset.sum_congr rfl
 intro a ha
 rw [prefix_weight decode D point w hw a hp]
 rfl

def source222 (point column : List Q) : Result (Option Q) :=
 PV_OWNI_RawConsumer.source point column (width point) (trailing point) (suffix point)

/-- Discharges the named scalar link for the complete raw source model. The
native association, input pipeline and byte-frame transcript links remain
separate obligations of restore; no dense value is assumed here. -/
theorem source_dense (decode : Q → K) (D : PV_OWNJ_DecodeFold.Decoder decode) :
 PV_OWNM_V239.PV_OWNM_Link_SourceDense decode zero source222 := by
 intro p c hl hp hc
 unfold source222
 rw [PV_OWNI_RawConsumer.result p c _ _ _ (PV_OWNI_Scanner.split p hl) (suffix_bound p)]
 simp only [bind_tc_ok]
 rw [PV_OWNJ_ValueBridge.value_commutes decode D p c hp hc]
 rw [sparse_dense decode D p c hl hp]

theorem concrete_source_dense :
 PV_OWNM_V239.PV_OWNM_Link_SourceDense PV_OWNK_ConcreteDecoder.decode zero source222 :=
 source_dense PV_OWNK_ConcreteDecoder.decode PV_OWNK_ConcreteDecoder.decoder

#print axioms concrete_source_dense
#print axioms take_coordinates
#print axioms prefix_weight
#print axioms scanner_suffix_length
#print axioms scanner_decoded_cast
#print axioms sparse_dense
#print axioms source_dense
open PV_OWNM_V239

/-- The scalar commutation hypothesis of the skeleton is discharged and consumed.
Actual-input, operational byte-frame and owned-source instances are still named
hypotheses, not silently supplied by independent model invariants. -/
theorem concrete_restore {W : Type}
 (wirePoints : List PV_OWNI_RawOps.Q → List (List PV_OWNI_RawOps.Q)) (isBoolean : PV_OWNI_RawOps.Q → Bool)
 (reconstruct879 reconstruct890 : Public → List PV_OWNI_RawOps.Q)
 (native : Input → List PV_OWNI_RawOps.Q → Nat → Execution PV_OWNK_ConcreteDecoder.K W)
 (resource : Input → List PV_OWNI_RawOps.Q → Nat → ResourceExit W)
 (failures : List Bool) (left right : Input)
 (inputL : PV_OWNM_Link_ActualInput wirePoints left)
 (inputR : PV_OWNM_Link_ActualInput wirePoints right)
 (cbL : PV_OWNM_Link_Transcript879 reconstruct879 left)
 (cbR : PV_OWNM_Link_Transcript879 reconstruct879 right)
 (finalL : PV_OWNM_Link_Transcript890 reconstruct890 left)
 (finalR : PV_OWNM_Link_Transcript890 reconstruct890 right)
 (ownedL : PV_OWNM_Link_OwnedPublicPlan PV_OWNK_ConcreteDecoder.decode PV_OWNN_SourceDense.source222
  wirePoints isBoolean native resource failures left)
 (ownedR : PV_OWNM_Link_OwnedPublicPlan PV_OWNK_ConcreteDecoder.decode PV_OWNN_SourceDense.source222
  wirePoints isBoolean native resource failures right)
 (samePublic : left.pubData = right.pubData) (sameSite : left.site = right.site)
 (sameLengths : left.columns.map List.length = right.columns.map List.length) :
 (∀ p ∈ wirePoints left.point, ∀ lane c, left.columns[lane]? = some c →
  native left p lane = attach (resource left p lane)
   (ok (if c.length ≠ 1024 then none else some (dense PV_OWNK_ConcreteDecoder.decode zero p c)))) ∧
 (∀ p ∈ wirePoints right.point, ∀ lane c, right.columns[lane]? = some c →
  native right p lane = attach (resource right p lane)
   (ok (if c.length ≠ 1024 then none else some (dense PV_OWNK_ConcreteDecoder.decode zero p c)))) ∧
 (∀ pL ∈ wirePoints left.point, ∀ pR ∈ wirePoints right.point,
  ∀ laneL laneR cL cR, left.columns[laneL]? = some cL →
  right.columns[laneR]? = some cR →
  (native left pL laneL).trace = (native right pR laneR).trace) :=
 PV_OWNM_V239.restore PV_OWNK_ConcreteDecoder.decode zero PV_OWNN_SourceDense.source222 wirePoints isBoolean
  reconstruct879 reconstruct890 native resource failures left right inputL inputR
  PV_OWNN_SourceDense.concrete_source_dense cbL cbR finalL finalR ownedL ownedR
  samePublic sameSite sameLengths

#print axioms concrete_restore
end R1Z.PV_OWNN_SourceDense
