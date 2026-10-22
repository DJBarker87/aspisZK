import R1Z.ProverCommitTerminalFactor51
import R1Z.ProverCommitQArray48
/-! Symbolic proof of the complete terminal equality-product loop. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTerminalProduct51
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)
attribute [local irreducible] ProverCommitNativeQ48.source ProverCommitQArray48.array

theorem go (a b : Nat → Old.Q)
    (ha : ∀ i, i<10 → Canonical (a i)) (hb : ∀ i, i<10 → Canonical (b i))
    (n : Nat) (index : U8) (hi : index.val+n=10) (acc : Old.Q) (hacc : Canonical acc) :
    ∃ z : Old.Q, terminal_eq51.go (ProverCommitQArray48.array 10#usize a)
      (ProverCommitQArray48.array 10#usize b) index (ProverCommitNativeQ48.source acc)=
        ok (ProverCommitNativeQ48.source z) ∧ Canonical z ∧
      decode z=decode acc*ProverCommitTerminalMath51.product (fun i => decode (a i)) (fun i => decode (b i)) n index.val := by
  induction n generalizing index acc with
  | zero =>
    have he : index=10#u8 := by scalar_tac
    refine ⟨acc,?_,hacc,?_⟩
    · rw [terminal_eq51.go,he];rfl
    · rw [ProverCommitTerminalMath51.product,mul_one]
  | succ n ih =>
    have hne : index≠10#u8 := by scalar_tac
    have hib : index.val<10 := by omega
    let idx := UScalar.cast .Usize index
    have hidx : idx.val=index.val := by scalar_tac
    have hinc : (U8.wrapping_add index 1#u8).val=index.val+1 := by
      rw [U8.wrapping_add_val_eq]
      have hs : UScalar.size .U8=256 := by rw [UScalar.size_def];decide
      rw [hs]
      change (index.val+1)%256=index.val+1
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨factor,hfactor,hcfactor,hdfactor⟩ := ProverCommitTerminalFactor51.exact_result
      (a index.val) (b index.val) (ha _ hib) (hb _ hib)
    obtain ⟨next,hnext,hcnext,hdnext⟩ := ProverCommitNativeQ48.mul acc factor hacc hcfactor
    obtain ⟨z,hz,hcz,hdz⟩ := ih (U8.wrapping_add index 1#u8) (by rw [hinc];omega) next hcnext
    refine ⟨z,?_,hcz,?_⟩
    · rw [terminal_eq51.go]
      simp only [hne,if_false,lift,bind_tc_ok]
      change (do
        let left ← Array.index_usize (ProverCommitQArray48.array 10#usize a) idx
        let right ← Array.index_usize (ProverCommitQArray48.array 10#usize b) idx
        let f ← terminal_eq51.factor left right
        let next ← field.QM31.mul (ProverCommitNativeQ48.source acc) f
        terminal_eq51.go (ProverCommitQArray48.array 10#usize a) (ProverCommitQArray48.array 10#usize b)
          (U8.wrapping_add index 1#u8) next)=_
      rw [ProverCommitQArray48.index _ _ idx (by rw [hidx];exact hib)]
      simp only [bind_tc_ok]
      rw [ProverCommitQArray48.index _ _ idx (by rw [hidx];exact hib)]
      simp only [bind_tc_ok,hidx,hfactor,hnext]
      exact hz
    · rw [hdz,hdnext,hdfactor,hinc,ProverCommitTerminalMath51.product]
      ring

#print axioms go
end R1Z.ProverCommitTerminalProduct51
