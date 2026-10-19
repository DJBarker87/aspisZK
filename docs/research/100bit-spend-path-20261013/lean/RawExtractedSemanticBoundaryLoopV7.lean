import AspisR1SemanticCallExtraction.Funs
import RawExtractedSemanticCallOpsV23
import RawSemanticPolynomialOps

set_option autoImplicit false
namespace AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7

open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV23
open AspisR1.ExtractedMaskQM31Exact

abbrev GenQ := AspisR1SemanticCallExtraction.aspis_core.field.QM31
abbrev Canonical := AspisR1.ExtractedMaskQM31Exact.CurrentCanonicalQM
abbrev ExactQ := AspisR1.ExtractedMaskQM31Exact.QM31Exact

def coefficients (p : Array GenQ 28#usize) : List ExactQ :=
  p.val.map (fun x => decode (genQToProbe x))

def prefixSum (xs : List ExactQ) (n : Nat) : ExactQ := (xs.take n).sum

private theorem array_index_usize_ok {α : Type} {n : Usize}
    (a : Array α n) (i : Usize) (hi : i.val < n.val) :
    Array.index_usize a i = .ok (a.val[i.val]'(by simpa [a.property] using hi)) := by
  have hidx : i.val < a.val.length := by simpa [a.property] using hi
  unfold Array.index_usize
  change (match a.val[i.val]? with
    | none => Result.fail Error.arrayOutOfBounds
    | some x => Result.ok x) = Result.ok (a.val[i.val]'hidx)
  rw [List.getElem?_eq_getElem hidx]

private theorem usize_add_result (a b : Usize) (hsum : a.val + b.val ≤ Usize.max) :
    ∃ c : Usize, UScalar.add a b = .ok c ∧ c.val = a.val + b.val := by
  have hchecked : (UScalar.add a b) ⦃ z => z.val = a.val + b.val ⦄ := by
    apply UScalar.add_spec
    simpa only [UScalar.max_USize_eq] using hsum
  obtain ⟨c, hc, hval⟩ := WP.spec_imp_exists hchecked
  exact ⟨c, hc, hval⟩

private theorem prefixSum_step (xs : List ExactQ) (i : Nat) (hi : i < xs.length) :
    prefixSum xs (i + 1) = prefixSum xs i + xs[i]'hi := by
  unfold prefixSum
  rw [List.take_succ_eq_append_getElem hi, List.sum_append]
  simp

private theorem prefixSum_length (xs : List ExactQ) : prefixSum xs xs.length = xs.sum := by
  simp [prefixSum]

theorem semantic_boundary_loop_refines
    (p : Array GenQ 28#usize) (seed : GenQ)
    (hseed : Canonical (genQToProbe seed))
    (hp : ∀ i : Nat, (hi : i < 28) →
      Canonical (genQToProbe (p.val[i]'(by simpa [p.property] using hi)))) :
    ∃ out : GenQ,
      AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop p seed 0#usize = .ok out ∧
      Canonical (genQToProbe out) ∧
      decode (genQToProbe out) =
        decode (genQToProbe seed) + (coefficients p).sum := by
  have hs : WP.spec
      (AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop p seed 0#usize)
      (fun out : GenQ => Canonical (genQToProbe out) ∧
        decode (genQToProbe out) =
          decode (genQToProbe seed) + prefixSum (coefficients p) 28) := by
    unfold AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop
    refine loop.spec_decr_nat
      (fun s : GenQ × Usize => 28 - s.2.val)
      (fun s => s.2.val ≤ 28 ∧ Canonical (genQToProbe s.1) ∧
        decode (genQToProbe s.1) =
          decode (genQToProbe seed) + prefixSum (coefficients p) s.2.val)
      (fun out : GenQ => Canonical (genQToProbe out) ∧
        decode (genQToProbe out) =
          decode (genQToProbe seed) + prefixSum (coefficients p) 28)
      (fun s : GenQ × Usize =>
        AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop.body p s.1 s.2)
      (seed, 0#usize) ?_ ⟨by change (0#usize).val ≤ 28; decide,
        hseed, by simp [prefixSum]⟩
    rintro ⟨acc, idx⟩ ⟨hiidx, hacc, hval⟩
    change idx.val ≤ 28 at hiidx
    change Canonical (genQToProbe acc) at hacc
    change decode (genQToProbe acc) =
      decode (genQToProbe seed) + prefixSum (coefficients p) idx.val at hval
    by_cases hi : idx.val < 28
    · have hguard : idx < 28#usize := by scalar_tac
      let q : GenQ := p.val[idx.val]'(by
        simpa [p.property] using hi)
      have hread : Array.index_usize p idx = .ok q := by
        simpa [q] using array_index_usize_ok p idx (by simpa [p.property] using hi)
      have hq : Canonical (genQToProbe q) := by
        exact hp idx.val hi
      obtain ⟨acc', hadd, hacc', hdecode⟩ := generated_qm_add_exact acc q hacc hq
      have hsum : idx.val + (1#usize).val ≤ Usize.max := by scalar_tac
      obtain ⟨idx', hidx, hidxval⟩ := usize_add_result idx 1#usize hsum
      have hprefixStep : prefixSum (coefficients p) (idx.val + 1) =
          prefixSum (coefficients p) idx.val + (coefficients p)[idx.val]'(by
            simp [coefficients, p.property]
            omega) := by
        apply prefixSum_step
      have hqdecode : (coefficients p)[idx.val]'(by
            simp [coefficients, p.property]
            omega) = decode (genQToProbe q) := by
        simp [coefficients, q]
      have hstep : decode (genQToProbe acc') =
          decode (genQToProbe acc) + decode (genQToProbe q) := hdecode
      have hone : (1#usize).val = 1 := by decide
      have hidxNat : idx'.val = idx.val + 1 := by rw [hidxval, hone]
      have hidx' : (idx + 1#usize : Result Usize) = Result.ok idx' := by
        exact hidx
      simp only [AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop.body,
        if_pos hguard, hread, hadd, bind_tc_ok, hidx']
      rw [WP.spec_ok]
      change ((idx'.val ≤ 28 ∧ Canonical (genQToProbe acc') ∧
        decode (genQToProbe acc') = decode (genQToProbe seed) +
          prefixSum (coefficients p) idx'.val) ∧
        28 - idx'.val < 28 - idx.val)
      refine ⟨⟨by omega, hacc', ?_⟩, by rw [hidxNat]; omega⟩
      rw [hidxNat, hstep, hval, ← hqdecode, hprefixStep]
      simp only [add_assoc]
    · have hguard : ¬ idx < 28#usize := by scalar_tac
      have heq : idx.val = 28 := by omega
      simp only [AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop.body,
        if_neg hguard]
      rw [WP.spec_ok]
      change Canonical (genQToProbe acc) ∧
        decode (genQToProbe acc) = decode (genQToProbe seed) +
          prefixSum (coefficients p) 28
      exact ⟨hacc, by simpa [heq] using hval⟩
  obtain ⟨out, hout, hprop⟩ := WP.spec_imp_exists hs
  refine ⟨out, hout, hprop.1, ?_⟩
  have hlen : (coefficients p).length = 28 := by
    simp [coefficients, p.property]
  rw [← hlen, prefixSum_length] at hprop
  exact hprop.2

#print axioms semantic_boundary_loop_refines

end AspisR1PublicPreparation.RawExtractedSemanticBoundaryLoopV7
