import RawPoseidonExternalRowWrapper
import RawPoseidonRowField
import ExtractedMaskQM31Exact

/-! The actual candidate row wrapper interpreted in the existing exact-field
Poseidon matrix model. No full matrix layer or terminal caller is asserted. -/
set_option autoImplicit false
namespace AspisR1.RawPoseidonExternalRowExact
open Aeneas Aeneas.Std Result
open AspisR1SelectedMaskProbe
open AspisR1.RawPoseidonExternalRowWrapper
open AspisR1.RawPoseidonExternalRowReads
open AspisR1.RawPoseidonExternalRows
open AspisR1.RawPoseidonRowField
open AspisR1.ExtractedMaskQM31Exact

/-- Source word coordinates, before reduction. The U32 input need not already
be a canonical field representative. -/
def inputWords (input : Input) (i j : Fin 4) : Nat :=
  ((rowValue input i).val[j.val]'(by
    simpa [(rowValue input i).property] using j.isLt)).val

private theorem small_nat_usize (n : Nat) (hn : n < 4) :
    n < 2 ^ Std.UScalarTy.Usize.numBits := by
  have hpow : 4 < 2 ^ Std.UScalarTy.Usize.numBits := by
    rw [Std.UScalarTy.Usize_numBits_eq, ← Usize.max_succ_eq_pow]
    have hmax := Usize.cMax_bound_concrete.1
    omega
  omega

/-- Every admitted row index executes successfully and returns the exact
mathematical matrix row on the decoded input. All raw arithmetic bounds and
canonicality of the output are derived by the preceding source proof. -/
theorem external_linear_lazy_row_exact
    (input : Input) (output : Usize) (houtput : output.val < 4) :
    ∃ q : field.QM31,
      state_only_poseidon.external_linear_lazy_row input output = .ok q ∧
      AspisR1.ExtractedMaskTowerAdd.CanonicalQM q ∧
      decode q = R0P.poseidonMat4
        (fun i => decodeWords (inputWords input i)) ⟨output.val, houtput⟩ := by
  let r : Fin 4 := ⟨output.val, houtput⟩
  obtain ⟨raw, q, hrun, hcanonical, hwords, hraw⟩ :=
    external_linear_lazy_row_words input r
  have hindex : output = Usize.ofNatCore r.val
      (small_nat_usize r.val r.isLt) := by
    apply UScalar.eq_of_val_eq
    simp [r, UScalar.ofNatCore_val_eq]
  have hrun' : state_only_poseidon.external_linear_lazy_row input output = .ok q := by
    rw [hindex]
    exact hrun
  have h0 := hraw (0 : Fin 4)
  have h1 := hraw (1 : Fin 4)
  have h2 := hraw (2 : Fin 4)
  have h3 := hraw (3 : Fin 4)
  change (raw.val[0]'_).val = rawRowNat (fun i => inputWords input i 0) r at h0
  change (raw.val[1]'_).val = rawRowNat (fun i => inputWords input i 1) r at h1
  change (raw.val[2]'_).val = rawRowNat (fun i => inputWords input i 2) r at h2
  change (raw.val[3]'_).val = rawRowNat (fun i => inputWords input i 3) r at h3
  have h0mod : (raw.val[0]'_).val % AspisV8R15.ExactTowerBase.P = rawRowNat (fun i => inputWords input i 0) r % AspisV8R15.ExactTowerBase.P :=
    congrArg (fun n : Nat => n % AspisV8R15.ExactTowerBase.P) h0
  have h1mod : (raw.val[1]'_).val % AspisV8R15.ExactTowerBase.P = rawRowNat (fun i => inputWords input i 1) r % AspisV8R15.ExactTowerBase.P :=
    congrArg (fun n : Nat => n % AspisV8R15.ExactTowerBase.P) h1
  have h2mod : (raw.val[2]'_).val % AspisV8R15.ExactTowerBase.P = rawRowNat (fun i => inputWords input i 2) r % AspisV8R15.ExactTowerBase.P :=
    congrArg (fun n : Nat => n % AspisV8R15.ExactTowerBase.P) h2
  have h3mod : (raw.val[3]'_).val % AspisV8R15.ExactTowerBase.P = rawRowNat (fun i => inputWords input i 3) r % AspisV8R15.ExactTowerBase.P :=
    congrArg (fun n : Nat => n % AspisV8R15.ExactTowerBase.P) h3
  have h00 := congrArg (fun x : (Nat × Nat) × (Nat × Nat) => x.1.1) hwords
  have h01 := congrArg (fun x : (Nat × Nat) × (Nat × Nat) => x.1.2) hwords
  have h10 := congrArg (fun x : (Nat × Nat) × (Nat × Nat) => x.2.1) hwords
  have h11 := congrArg (fun x : (Nat × Nat) × (Nat × Nat) => x.2.2) hwords
  change q.c0.a.val = (raw.val[0]'_).val % AspisR1.ExtractedMaskTowerAdd.P at h00
  change q.c0.b.val = (raw.val[1]'_).val % AspisR1.ExtractedMaskTowerAdd.P at h01
  change q.c1.a.val = (raw.val[2]'_).val % AspisR1.ExtractedMaskTowerAdd.P at h10
  change q.c1.b.val = (raw.val[3]'_).val % AspisR1.ExtractedMaskTowerAdd.P at h11
  have hdecode : decode q = decodeWords
      (fun j => rawRowNat (fun i => inputWords input i j) r %
        AspisV8R15.ExactTowerBase.P) := by
    apply QuadraticAlgebra.ext
    · apply QuadraticAlgebra.ext
      · change (q.c0.a.val : M) = _
        rw [h00]
        exact congrArg (fun n : Nat => (n : M)) h0mod
      · change (q.c0.b.val : M) = _
        rw [h01]
        exact congrArg (fun n : Nat => (n : M)) h1mod
    · apply QuadraticAlgebra.ext
      · change (q.c1.a.val : M) = _
        rw [h10]
        exact congrArg (fun n : Nat => (n : M)) h2mod
      · change (q.c1.b.val : M) = _
        rw [h11]
        exact congrArg (fun n : Nat => (n : M)) h3mod
  refine ⟨q, hrun', hcanonical, ?_⟩
  rw [hdecode, decodeWords_mod, raw_rows_decode_eq_poseidonMat4]

#print axioms external_linear_lazy_row_exact
end AspisR1.RawPoseidonExternalRowExact
