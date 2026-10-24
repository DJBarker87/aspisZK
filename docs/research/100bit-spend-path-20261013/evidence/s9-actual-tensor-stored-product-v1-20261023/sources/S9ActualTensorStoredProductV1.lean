import S9ActualTensorOuterSemanticsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualTensorStoredProductV1
open AspisR1S9ActualTensorArithmeticV1 AspisR1S9TensorIndexedMeaningV1
open AspisR1S9ActualTensorWriteTraceV1 AspisR1S9ActualTensorOuterSemanticsV1
abbrev Can := AspisR1S9ActualPairQMHelperTransportV1.Canonical

def storedFactor (self : weights.Weights) (k : Usize) (d i : Nat) : ExactQM :=
  match self.factors.val[k.val]? with
  | none => 0
  | some row => match row.val[d]? with
    | none => 0
    | some coeffs => match coeffs.val[i]? with
      | none => 0
      | some q => decode q

private theorem array_read_lookup {A : Type} {n : Usize} (a : Array A n) (i : Usize) (v : A)
    (h : Array.index_usize a i = .ok v) : a.val[i.val]?=some v := by
  unfold Array.index_usize at h
  cases hr : a[i]? with
  | none => simp [hr] at h
  | some original =>
    rw [hr] at h
    have he : original=v := Result.ok.inj h
    exact he ▸ (by simpa using hr)

theorem stored_factor_read (self : weights.Weights) (k d i : Usize)
    (row : Row) (coeffs : Array Q 4#usize) (q : Q)
    (hr : Array.index_usize self.factors k = .ok row)
    (hc : Array.index_usize row d = .ok coeffs)
    (hq : Array.index_usize coeffs i = .ok q) :
    storedFactor self k d.val i.val=decode q := by
  unfold storedFactor
  simp only [array_read_lookup _ _ _ hr,array_read_lookup _ _ _ hc,array_read_lookup _ _ _ hq]

/-- Actual successful native tensor call computes the decoded product of its
OWN stored factor entries. Only canonicality of native field inputs is needed;
there is no independent factor-meaning contract. The separate constructor
semantics theorem can rewrite these exact stored factors to protocol factors. -/
theorem actual_tensor_success_stored_product (self : weights.Weights) (k : Usize)
    (input out : Slice Q)
    (hcan : ∀ (d : Usize) (row : Row) (coeffs : Array Q 4#usize) (i : Usize) (q : Q),
      Array.index_usize self.factors k = .ok row → Array.index_usize row d = .ok coeffs →
      Array.index_usize coeffs i = .ok q → Can q)
    (h : weights.Weights.tensor self k 2#usize input = .ok out) :
    MeaningOn decode (highProduct (storedFactor self k)) (fun i => i<64) out := by
  apply actual_tensor_s2_success_high_product (storedFactor self k) self k input out _ h
  intro d row coeffs i q hr hc hq
  exact ⟨hcan d row coeffs i q hr hc hq,(stored_factor_read self k d i row coeffs q hr hc hq).symm⟩

#print axioms stored_factor_read
#print axioms actual_tensor_success_stored_product
end AspisR1S9ActualTensorStoredProductV1
