import R1Z.ProverCommitGammaModel53
import R1Z.ProverCommitWideBasis51
/-! Actual owned coefficient permutations supply every gamma-batch input.
The per-column source Results remain conclusions; native Vec assembly is separate. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitGammaCoefficients53
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitSubfieldOps47
open ProverCommitWideOps48 ProverCommitMix48
open AspisR1.ExtractedCurrentQM31Exact (decode QM31Exact)

variable (c : Nat → Nat → Old.Q) (hc : ∀ l, l<29 → ∀ j, j<1024 → Canonical (c l j))

def trace : R0P.Trace QM31Exact := fun l j => decode (c l.val j.val)

def column (l : Fin 29) : Nat → Old.Q :=
  Classical.choose (ProverCommitCoefficientModel51.exact_result (c l.val) (hc l.val l.isLt)
    (trace c) l (fun _ => rfl))

def coefficient (l j : Nat) : Old.Q :=
  if h : l<29 then column c hc ⟨l,h⟩ j else zero

theorem column_spec (l : Fin 29) :
    coefficients51.eval (ProverCommitQArray48.array 1024#usize (c l.val))=
      ok (ProverCommitQArray48.array 1024#usize (coefficient c hc l.val)) ∧
    (∀ j, j<1024 → Canonical (coefficient c hc l.val j)) ∧
    ∀ j : Fin 1024, decode (coefficient c hc l.val j.val)=
      R0P.SemSource.coeffsOf AspisR1.rowEquiv (trace c) l j := by
  have hfun : coefficient c hc l.val=column c hc l := by
    funext j
    simp only [coefficient,dif_pos l.isLt]
  rw [hfun]
  exact Classical.choose_spec (ProverCommitCoefficientModel51.exact_result (c l.val) (hc l.val l.isLt)
    (trace c) l (fun _ => rfl))

def wide (l j : Nat) : Raw := (coefficient c hc l j,zero)
def wideTrace : R0P.Trace Exact := fun l j => ProverCommitWideBasis51.embed (trace c l j)

theorem wide_canonical (l : Nat) (hl : l<29) (j : Nat) (hj : j<1024) :
    canonical (wide c hc l j) :=
  ⟨(column_spec c hc ⟨l,hl⟩).2.1 j hj,zero_canonical⟩

theorem wide_value (l : Fin 29) (j : Fin 1024) :
    value (wide c hc l.val j.val)=R0P.SemSource.coeffsOf AspisR1.rowEquiv (wideTrace c) l j := by
  change ProverCommitWideBasis51.embed (decode (coefficient c hc l.val j.val))=_
  exact congrArg ProverCommitWideBasis51.embed ((column_spec c hc l).2.2 j)

theorem exact_result (x : Raw) (hx : canonical x)
    (ch : R0Z.HonestView.Challenges Exact) (hg : value x=ch.opening 0) :
    ∃ out : Nat → Raw,
      ProverCommitGammaOutput53.run (ProverCommitGammaCell53.table (wide c hc)) (source x)=
        ok (sourceArray 1024#usize out) ∧
      (∀ j, j<1024 → canonical (out j)) ∧
      ∀ j : Fin 1024, value (out j.val)=R1Z.Batched.batchR1 AspisR1.rowEquiv ch (wideTrace c) j := by
  exact ProverCommitGammaModel53.exact_result (wide c hc) (wide_canonical c hc) x hx
    (wideTrace c) (wide_value c hc) ch hg

#print axioms column_spec
#print axioms wide_canonical
#print axioms wide_value
#print axioms exact_result
end R1Z.ProverCommitGammaCoefficients53
