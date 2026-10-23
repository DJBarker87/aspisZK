import S9ActualTensorInnerSemanticsV1
import S9ActualTensorOuterPrefixV1
import S9ActualPairQMOutputCanonicalV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualTensorOuterSemanticsV1
open AspisR1S9ActualTensorArithmeticV1 AspisR1S9TensorIndexedMeaningV1
open AspisR1S9ActualTensorWriteTraceV1 AspisR1S9MarkedSliceUpdateV1
open AspisR1S9ActualTensorSemanticCellV1 AspisR1S9ActualTensorInnerSemanticsV1
open AspisR1S9ActualTensorOuterPrefixV1
abbrev Can := AspisR1S9ActualPairQMHelperTransportV1.Canonical

def stageValues (factor : Nat → Nat → ExactQM) : Nat → ExactQM :=
  expanded (expanded (expanded (fun _ => 1) (factor 2) 1) (factor 3) 4) (factor 4) 16

def highProduct (factor : Nat → Nat → ExactQM) (i : Nat) : ExactQM :=
  factor 2 (i%4) * factor 3 ((i/4)%4) * factor 4 ((i/16)%4)

theorem stage_values_eq_high_product (factor : Nat → Nat → ExactQM) (i : Nat) (hi : i<64) :
    stageValues factor i = highProduct factor i := by
  have h0 : (i%16)%4=i%4 := by omega
  have h1 : (i%16)/4=(i/4)%4 := by omega
  have h2 : (i/16)%4=i/16 := by omega
  simp only [stageValues,expanded,highProduct,Nat.mod_one,Nat.div_one,one_mul,h0,h1,h2]

/-- Exactly the three source outer iterations d=2,3,4. The semantic inner
invariant proves all64 cells symbolically; no concrete cell list is unfolded. -/
theorem outer_three_stage_semantics (factor : Nat → Nat → ExactQM)
    (self : weights.Weights) (k : Usize) (input out : Slice Q)
    (hin : MeaningOn decode (fun _ => 1) (fun i => i<1) input)
    (hcan : GoodOn Can (fun i => i<1) input)
    (hfactors : ∀ (d : Usize) (row : Row) (coeffs : Array Q 4#usize) (i : Usize) (q : Q),
      Array.index_usize self.factors k = .ok row → Array.index_usize row d = .ok coeffs →
      Array.index_usize coeffs i = .ok q → Can q ∧ decode q=factor d.val i.val)
    (h : weights.Weights.tensor_loop0 ({start:=2#usize,«end»:=5#usize} : Front)
      self k input 1#usize = .ok out) :
    MeaningOn decode (highProduct factor) (fun i => i<64) out := by
  have h14 : Usize.wrapping_mul 1#usize 4#usize=4#usize := by
    apply UScalar.eq_of_val_eq; rw [wrapping_mul_four_val _ (by simp)]; rfl
  have h416 : Usize.wrapping_mul 4#usize 4#usize=16#usize := by
    apply UScalar.eq_of_val_eq; rw [wrapping_mul_four_val _ (by simp)]; rfl
  have h1664 : Usize.wrapping_mul 16#usize 4#usize=64#usize := by
    apply UScalar.eq_of_val_eq; rw [wrapping_mul_four_val _ (by simp)]; rfl
  obtain ⟨w1,s1,hi1,ho1⟩ := outer_step_success
    ({start:=2#usize,«end»:=5#usize} : Front) ({start:=3#usize,«end»:=5#usize} : Front)
    2#usize k 1#usize self input out (next_some_fixed _ _ _ (by simp) (by simp)) h
  obtain ⟨hw1,hm1,hc1⟩ := tensor_inner_semantics (fun _ => 1) (factor 2) self k 1#usize 2#usize
    _ input s1 w1 (by simp) (by simp) (by simp) rfl hin hcan (hfactors 2#usize) hi1
  subst w1
  rw [h14] at ho1
  have hm4 : MeaningOn decode (expanded (fun _ => 1) (factor 2) 1) (fun i => i<4) s1 := by simpa using hm1
  have hc4 : GoodOn Can (fun i => i<4) s1 := by simpa using hc1
  obtain ⟨w2,s2,hi2,ho2⟩ := outer_step_success
    ({start:=3#usize,«end»:=5#usize} : Front) ({start:=4#usize,«end»:=5#usize} : Front)
    3#usize k 4#usize self s1 out (next_some_fixed _ _ _ (by simp) (by simp)) ho1
  obtain ⟨hw2,hm2,hc2⟩ := tensor_inner_semantics (expanded (fun _ => 1) (factor 2) 1)
    (factor 3) self k 4#usize 3#usize _ s1 s2 w2 (by simp) (by simp) (by simp) rfl
    hm4 hc4 (hfactors 3#usize) hi2
  subst w2
  rw [h416] at ho2
  have hm16 : MeaningOn decode (expanded (expanded (fun _ => 1) (factor 2) 1) (factor 3) 4)
      (fun i => i<16) s2 := by simpa using hm2
  have hc16 : GoodOn Can (fun i => i<16) s2 := by simpa using hc2
  obtain ⟨w3,s3,hi3,ho3⟩ := outer_step_success
    ({start:=4#usize,«end»:=5#usize} : Front) ({start:=5#usize,«end»:=5#usize} : Front)
    4#usize k 16#usize self s2 out (next_some_fixed _ _ _ (by simp) (by simp)) ho2
  obtain ⟨hw3,hm3,hc3⟩ := tensor_inner_semantics
    (expanded (expanded (fun _ => 1) (factor 2) 1) (factor 3) 4) (factor 4)
    self k 16#usize 4#usize _ s2 s3 w3 (by simp) (by simp) (by simp) rfl
    hm16 hc16 (hfactors 4#usize) hi3
  subst w3
  rw [h1664] at ho3
  have hout := outer_done_success 5#usize k 64#usize self s3 out ho3
  rw [hout]
  intro i q hr hi
  have hm := hm3 i q hr (by simpa using hi)
  exact hm.trans (stage_values_eq_high_product factor i.val hi)

private theorem bind_success {A B : Type} (m : Result A) (f : A → Result B)
    (out : B) (h : (do let a ← m; f a) = .ok out) :
    ∃ a, m=.ok a ∧ f a=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok a => exact ⟨a,rfl,h⟩

/-- The actual native S2 tensor's decoded values are products of the exact
three stored source factor digits. The only mathematical input contract is
what those stored factor reads mean; arbitrary old scratch is permitted. -/
theorem actual_tensor_s2_success_high_product (factor : Nat → Nat → ExactQM)
    (self : weights.Weights) (k : Usize) (input out : Slice Q)
    (hfactors : ∀ (d : Usize) (row : Row) (coeffs : Array Q 4#usize) (i : Usize) (q : Q),
      Array.index_usize self.factors k = .ok row → Array.index_usize row d = .ok coeffs →
      Array.index_usize coeffs i = .ok q → Can q ∧ decode q=factor d.val i.val)
    (h : weights.Weights.tensor self k 2#usize input = .ok out) :
    MeaningOn decode (highProduct factor) (fun i => i<64) out := by
  unfold weights.Weights.tensor at h
  obtain ⟨s,hs,hloop⟩ := bind_success _ _ _ h
  have hm := update_meaning_on decode (fun _ => 1) (fun _ => False) (fun i => i<1)
    input s 0#usize aspis_core.field.QM31.ONE (by intro i v hr hm; cases hm)
    native_one_decode (by intro i hi; exact Or.inl (by simp; omega)) hs
  have hc := update_good_on Can (fun _ => False) (fun i => i<1)
    input s 0#usize aspis_core.field.QM31.ONE (by intro i v hr hm; cases hm)
    AspisR1S9ActualPairQMOutputCanonicalV1.one_canonical
    (by intro i hi; exact Or.inl (by simp; omega)) hs
  exact outer_three_stage_semantics factor self k s out hm hc.2 hfactors hloop

#print axioms stage_values_eq_high_product
#print axioms outer_three_stage_semantics
#print axioms actual_tensor_s2_success_high_product
end AspisR1S9ActualTensorOuterSemanticsV1
