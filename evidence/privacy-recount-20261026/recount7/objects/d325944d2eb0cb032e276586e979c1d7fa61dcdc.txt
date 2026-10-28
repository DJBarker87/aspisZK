import R1Z.ProverRwDictionaryTower
import AspisR1ProducerRelease47.Interpolate48
import AspisR1ProducerRelease47.Samples49
import AspisR1ProducerRelease47.Kernels49
import AspisR1ProducerRelease47.Batched48

/-! Retained release arithmetic and scalar macro bodies. This selector replaces
its predecessor's checked-arithmetic M31 entries with the release extraction's
wrapping operations. This does not assert an unrestricted checked/release
identity. Source feature/ABI association remains explicit in the handoff. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwDictionaryScalar
open Aeneas Aeneas.Std Result ProverRwFull ProverRwDictionaryTower
-- The two from_m31 bodies are the literal retained generic54 source bodies,
-- with only the earlier operation name qualified to this local declaration.
def mFrom (value : U32) : Result U32 := do
  let i ← value % AspisR1ProducerRelease47.field.P
  .ok i

def qFrom (value : U32) : Result NQ := do
  let m ← mFrom value
  let c ← AspisR1ProducerRelease47.field.CM31.from_m31 m
  AspisR1ProducerRelease47.field.QM31.from_cm31 c

variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwDictionaryTower.selected ops with
    op42 := .ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO)
    op52 := (fun a b => mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul_m31 (toW a) b))
    op55 := .ok AspisR1ProducerRelease47.field.M31.ZERO
    op56 := .ok AspisR1ProducerRelease47.field.M31.ONE
    op57 := AspisR1ProducerRelease47.field.M31.mul
    op58 := AspisR1ProducerRelease47.field.M31.double
    op59 := AspisR1ProducerRelease47.inverse_ref
    op61 := (fun a => mapResult fromC (AspisR1ProducerRelease47.field.CM31.from_m31 a))
    op65 := .ok (fromQ AspisR1ProducerRelease47.field.QM31.ONE)
    op66 := (fun c => mapResult fromQ (AspisR1ProducerRelease47.field.QM31.from_cm31 (toC c)))
    op70 := (fun a b => mapResult fromQ (AspisR1ProducerRelease47.field.QM31.mul_m31 (toQ a) b))
    op73 := AspisR1ProducerRelease47.field.M31.add
    op74 := AspisR1ProducerRelease47.field.M31.sub
    op87 := .ok AspisR1ProducerRelease47.field.M31.ZERO
    op88 := .ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO)
    op89 := .ok (fromQ AspisR1ProducerRelease47.field.QM31.ZERO)
    op90 := .ok AspisR1ProducerRelease47.field.M31.ONE
    op91 := .ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE)
    op92 := .ok (fromQ AspisR1ProducerRelease47.field.QM31.ONE)
    op93 := AspisR1ProducerRelease47.field.M31.add
    op94 := wAdd
    op95 := qAdd
    op96 := AspisR1ProducerRelease47.field.M31.sub
    op97 := (fun a b => mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub (toW a) (toW b)))
    op98 := qSub
    op99 := AspisR1ProducerRelease47.field.M31.neg
    op102 := AspisR1ProducerRelease47.field.M31.mul
    op103 := wMul
    op104 := qMul
    op106 := mFrom
    op108 := (fun a => mapResult fromQ (qFrom a))}

theorem entry42 (ops : ExternalFuns) :
    (selected ops).op42 = .ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) := rfl

theorem entry52 (ops : ExternalFuns) :
    (selected ops).op52 = (fun a b => mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.mul_m31 (toW a) b)) := rfl

theorem entry55 (ops : ExternalFuns) :
    (selected ops).op55 = .ok AspisR1ProducerRelease47.field.M31.ZERO := rfl

theorem entry56 (ops : ExternalFuns) :
    (selected ops).op56 = .ok AspisR1ProducerRelease47.field.M31.ONE := rfl

theorem entry57 (ops : ExternalFuns) :
    (selected ops).op57 = AspisR1ProducerRelease47.field.M31.mul := rfl

theorem entry58 (ops : ExternalFuns) :
    (selected ops).op58 = AspisR1ProducerRelease47.field.M31.double := rfl

theorem entry59 (ops : ExternalFuns) :
    (selected ops).op59 = AspisR1ProducerRelease47.inverse_ref := rfl

theorem entry61 (ops : ExternalFuns) :
    (selected ops).op61 = (fun a => mapResult fromC (AspisR1ProducerRelease47.field.CM31.from_m31 a)) := rfl

theorem entry65 (ops : ExternalFuns) :
    (selected ops).op65 = .ok (fromQ AspisR1ProducerRelease47.field.QM31.ONE) := rfl

theorem entry66 (ops : ExternalFuns) :
    (selected ops).op66 = (fun c => mapResult fromQ (AspisR1ProducerRelease47.field.QM31.from_cm31 (toC c))) := rfl

theorem entry70 (ops : ExternalFuns) :
    (selected ops).op70 = (fun a b => mapResult fromQ (AspisR1ProducerRelease47.field.QM31.mul_m31 (toQ a) b)) := rfl

theorem entry73 (ops : ExternalFuns) :
    (selected ops).op73 = AspisR1ProducerRelease47.field.M31.add := rfl

theorem entry74 (ops : ExternalFuns) :
    (selected ops).op74 = AspisR1ProducerRelease47.field.M31.sub := rfl

theorem entry87 (ops : ExternalFuns) :
    (selected ops).op87 = .ok AspisR1ProducerRelease47.field.M31.ZERO := rfl

theorem entry88 (ops : ExternalFuns) :
    (selected ops).op88 = .ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ZERO) := rfl

theorem entry89 (ops : ExternalFuns) :
    (selected ops).op89 = .ok (fromQ AspisR1ProducerRelease47.field.QM31.ZERO) := rfl

theorem entry90 (ops : ExternalFuns) :
    (selected ops).op90 = .ok AspisR1ProducerRelease47.field.M31.ONE := rfl

theorem entry91 (ops : ExternalFuns) :
    (selected ops).op91 = .ok (fromW AspisR1ProducerRelease47.field.wide_exact.WideExact.ONE) := rfl

theorem entry92 (ops : ExternalFuns) :
    (selected ops).op92 = .ok (fromQ AspisR1ProducerRelease47.field.QM31.ONE) := rfl

theorem entry93 (ops : ExternalFuns) :
    (selected ops).op93 = AspisR1ProducerRelease47.field.M31.add := rfl

theorem entry94 (ops : ExternalFuns) :
    (selected ops).op94 = wAdd := rfl

theorem entry95 (ops : ExternalFuns) :
    (selected ops).op95 = qAdd := rfl

theorem entry96 (ops : ExternalFuns) :
    (selected ops).op96 = AspisR1ProducerRelease47.field.M31.sub := rfl

theorem entry97 (ops : ExternalFuns) :
    (selected ops).op97 = (fun a b => mapResult fromW (AspisR1ProducerRelease47.field.wide_exact.WideExact.sub (toW a) (toW b))) := rfl

theorem entry98 (ops : ExternalFuns) :
    (selected ops).op98 = qSub := rfl

theorem entry99 (ops : ExternalFuns) :
    (selected ops).op99 = AspisR1ProducerRelease47.field.M31.neg := rfl

theorem entry102 (ops : ExternalFuns) :
    (selected ops).op102 = AspisR1ProducerRelease47.field.M31.mul := rfl

theorem entry103 (ops : ExternalFuns) :
    (selected ops).op103 = wMul := rfl

theorem entry104 (ops : ExternalFuns) :
    (selected ops).op104 = qMul := rfl

theorem entry106 (ops : ExternalFuns) :
    (selected ops).op106 = mFrom := rfl

theorem entry108 (ops : ExternalFuns) :
    (selected ops).op108 = (fun a => mapResult fromQ (qFrom a)) := rfl

#print axioms entry42
#print axioms entry52
#print axioms entry55
#print axioms entry56
#print axioms entry57
#print axioms entry58
#print axioms entry59
#print axioms entry61
#print axioms entry65
#print axioms entry66
#print axioms entry70
#print axioms entry73
#print axioms entry74
#print axioms entry87
#print axioms entry88
#print axioms entry89
#print axioms entry90
#print axioms entry91
#print axioms entry92
#print axioms entry93
#print axioms entry94
#print axioms entry95
#print axioms entry96
#print axioms entry97
#print axioms entry98
#print axioms entry99
#print axioms entry102
#print axioms entry103
#print axioms entry104
#print axioms entry106
#print axioms entry108
end R1Z.ProverRwDictionaryScalar
