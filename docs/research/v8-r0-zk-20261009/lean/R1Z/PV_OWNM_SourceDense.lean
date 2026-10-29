import R1Z.PV_OWNM_V239
import R1Z.PV_OWNM_DenseRows
import R1Z.PV_OWNM_FoldSum
import R1Z.PV_OWNL_Suffix
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNM_SourceDense
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
 simpa only [List.length_ofFn,weight,tail,List.get_eq_getElem,List.getElem_ofFn] using hprod

theorem sparse_dense (decode : Q → K) (D : PV_OWNJ_DecodeFold.Decoder decode)
 (point column : List Q) (hl : point.length=10)
 (hp : ∀ q ∈ point, PV_OWNJ_DecodeFold.Canon q) :
 PV_OWNJ_ValueBridge.sparse decode point column = PV_OWNM_V239.dense decode zero point column := by
 let w := width point
 let t := trailing point
 have split : w+t=10 := PV_OWNI_Scanner.split point hl
 have hw : w ≤ point.length := by omega
 have htlen : (point.drop w).length = t := by rw [List.length_drop]; omega
 let suffix : Fin (2^t) := ⟨PV_OWNI_Scanner.suffix point,suffix_bound point⟩
 have hs : ∀ i : Fin t,
  decode (point[(Fin.natAdd w i).val]?.getD zero) = if tail t suffix i then 1 else 0 := by
  intro i
  have hi : i.val < (point.drop w).length := by rw [htlen]; exact i.isLt
  have hd := PV_OWNL_Suffix.scanner_decoded decode D.zero_eq D.one_eq point ⟨i.val,hi⟩
  have hb : w+i.val < point.length := by omega
  simpa only [List.get_eq_getElem,List.getElem_drop,htlen,Fin.coe_natAdd,
   List.getElem?_eq_getElem hb,Option.getD_some,tail,suffix] using hd
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
 rw [← hd,PV_OWNM_FoldSum.sparse_sum]
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

#print axioms take_coordinates
#print axioms prefix_weight
#print axioms sparse_dense
#print axioms source_dense
end R1Z.PV_OWNM_SourceDense
