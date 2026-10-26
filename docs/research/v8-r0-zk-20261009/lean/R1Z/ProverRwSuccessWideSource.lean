import R1Z.ProverRwSuccessQuarticOperations
import R1Z.ProverRwSuccessVectors
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessWideSource
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
-- Value-level source port of scalar.rs and WideExact::{new,neg}. Arithmetic
-- is the retained release interpretation; CT/native/ABI association is separate.
def normalize (x : Q) : Result Q := mapResult fromQ
  (AspisR1ProducerRelease47.field.wide_exact.canonical_qm31 (toQ x))
def construct (a b : Q) : Result W := do
  let a' ← normalize a
  let b' ← normalize b
  .ok ⟨a',b'⟩
def neg (x : W) : Result W := do
  let a ← ProverRwSuccessInverseInstall.Src.qNeg x.c0
  let b ← ProverRwSuccessInverseInstall.Src.qNeg x.c1
  .ok ⟨a,b⟩
def u : Q := ⟨⟨0#u32,0#u32⟩,⟨1#u32,0#u32⟩⟩
def inverse (x : W) : Result (Option W) := do
  let a ← qMul x.c0 x.c0
  let b ← qMul x.c1 x.c1
  let ub ← qMul u b
  let norm ← qSub a ub
  let inverse ← ProverRwSuccessInverseInstall.Src.qInv norm
  let cf ← ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitTry.branch inverse
  match cf with
  | .Continue ni =>
    let lo ← qMul x.c0 ni
    let nb ← ProverRwSuccessInverseInstall.Src.qNeg x.c1
    let hi ← qMul nb ni
    let out ← construct lo hi
    .ok (some out)
  | .Break residual =>
    ProverRwDictionaryOptionSource.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionInfallible.from_residual W residual

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessVectors.selected ops with op100 := neg,op109 := inverse}
theorem neg_installed (ops : ExternalFuns) (x : W) : (selected ops).op100 x=neg x := rfl
theorem inverse_installed (ops : ExternalFuns) (x : W) : (selected ops).op109 x=inverse x := rfl
#print axioms neg_installed
#print axioms inverse_installed
end R1Z.ProverRwSuccessWideSource
