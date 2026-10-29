import R1Z.PV_OWNK_ConcreteDecoder
import R1Z.PV_OWNL_PrefixProduct
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNM_FoldSum
open scoped BigOperators
open PV_OWNI_RawOps
variable {K : Type} [Field K]

theorem fold_sum {A : Type} (xs : List A) (f : A → K) (initial : K) :
 xs.foldl (fun sum x => sum+f x) initial = initial+(xs.map f).sum := by
 induction xs generalizing initial with
 | nil => simp only [List.foldl_nil,List.map_nil,List.sum_nil,add_zero]
 | cons x xs ih =>
  simp only [List.foldl_cons,List.map_cons,List.sum_cons,ih,add_assoc]

theorem range_sum (n : Nat) (f : Nat → K) :
 ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
 rw [← List.map_coe_finRange_eq_range]
 simp only [List.map_map]
 exact (Fin.sum_univ_def (fun i : Fin n => f i.val)).symm

/-- No column lookup is replaced by a different index; the source integer
range and ordered additive fold become precisely the finite row sum. -/
theorem sparse_sum (decode : Q → K) (point column : List Q) :
 PV_OWNJ_ValueBridge.sparse decode point column =
 ∑ a : Fin (2^PV_OWNI_Scanner.width point),
  decode (((point.take (PV_OWNI_Scanner.width point)).foldl
   (PV_OWNI_WeightTotal.step (PV_OWNI_Scanner.width point) a.val) (ops.one,0)).1) *
  decode (column[PV_RDB2D_SparseAddress.row a.val (PV_OWNI_Scanner.trailing point)
   (PV_OWNI_Scanner.suffix point)]?.getD zero) := by
 unfold PV_OWNJ_ValueBridge.sparse PV_OWNI_BuildTotal.entries
 rw [List.foldl_map]
 rw [fold_sum]
 simp only [zero_add]
 exact range_sum _ _

/-- The decoded concrete raw prefix fold is the finite prefix product. -/
theorem prefix_product (decode : Q → K) (D : PV_OWNJ_DecodeFold.Decoder decode)
 (point : List Q) (width pref : Nat)
 (hc : ∀ q ∈ point, PV_OWNJ_DecodeFold.Canon q) :
 decode (((point.take width).foldl (PV_OWNI_WeightTotal.step width pref) (ops.one,0)).1) =
 ∏ i : Fin ((point.take width).map decode).length,
  if pref.testBit (width-1-i.val) then ((point.take width).map decode).get i
  else 1-((point.take width).map decode).get i := by
 rw [one_value]
 have h := PV_OWNJ_DecodeWeight.weight decode D width pref (point.take width) (one,0)
  D.one_canon (fun q hq => hc q (List.mem_of_mem_take hq))
 have hh := congrArg (fun x : K × Nat => x.1) h.2
 simp only [D.one_eq] at hh
 rw [hh]
 change (((point.take width).map decode).foldl (PV_OWNL_PrefixProduct.step width pref) (1,0)).1 = _
 rw [PV_OWNL_PrefixProduct.fold_product,one_mul,PV_OWNL_PrefixProduct.factors_product]
 simp only [Nat.zero_add]

#print axioms fold_sum
#print axioms range_sum
#print axioms sparse_sum
#print axioms prefix_product
end R1Z.PV_OWNM_FoldSum
