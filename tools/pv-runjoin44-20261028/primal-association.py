from pathlib import Path
for name,inp,out,counter in [('First',1024,256,'u16'),('Second',256,64,'u8')]:
 method=name.lower()
 s=f'''import R1Z.PV_RunJoin_FoldCallerValue44
import R1Z.ProverCommitFoldOutput48
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Primal{name}44
open Aeneas Aeneas.Std Result ProverRwFull
open ProverCommitWideOps48 ProverCommitMix48 PV_RunJoin_WideArithmetic44
open PV_RunJoin_FoldCell44 (array)
variable [ExternalTypes]

theorem complete (ops : ExternalFuns) (q : Nat → Raw) (hq : ∀ j, j < {inp} → canonical (q j))
    (a : Raw) (ha : canonical a) :
    ∃ (z : Nat → Raw) (out : alloc.vec.Vec W),
      @prover.fold _ (ProverRwP6BodyCandidate.selected ops) (Array.to_slice (array {inp}#usize q))
        (current (source a)) false = .ok out ∧
      AspisR1ProducerRelease47.fold_{method} (sourceArray {inp}#usize q) (source a)
        (Array.repeat {out}#usize AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) 0#usize {out}#{counter} =
        .ok (sourceArray {out}#usize z) ∧
      Array.to_slice (array {out}#usize z) = alloc.vec.Vec.deref out ∧
      (∀ j, j < {out} → canonical (z j)) ∧
      ∀ j, j < {out} → value (z j) = ProverCommitFoldOutput48.mathCell (fun i => value (q i)) (value a) j := by
  obtain ⟨z,hz,hcz,hdz⟩ := ProverCommitFoldOutput48.{method}_exact q hq a ha
  obtain ⟨out,hout,himage⟩ := PV_RunJoin_FoldCallerValue44.complete ops {inp}#usize {out}#usize rfl (by decide)
    q z a false hq ha hcz (fun j hj => by
      simpa only [ProverCommitFoldOutput48.mathCell,PV_RunJoin_FoldStepValue44.model,
        Bool.false_eq_true,↓reduceIte,PV_RunJoin_FoldCell44.polynomial,Nat.add_zero] using hdz j hj)
  exact ⟨z,out,hout,hz,himage,hcz,hdz⟩
#print axioms complete
end R1Z.PV_RunJoin_Primal{name}44
'''
 Path(f'docs/research/v8-r0-zk-20261009/lean/R1Z/PV_RunJoin_Primal{name}44.lean').write_text(s)
