-- Concrete callee bindings for the imported actual-body extraction. No axioms
-- and no callback hypotheses. Their composition domains are separate goals.
import NEV_AccumulateRaw.Types
import NEV_CodeFieldRaw.Funs
import NEI_LineFull.Funs
import NEI_PushRaw.Funs
import FIo_NativeFuns
set_option autoImplicit false
noncomputable section
namespace NEV_AccumulateRaw
open Aeneas Aeneas.Std Result
namespace NEV_Bindings
abbrev Q := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact

def toCtorQ (q : Q) : NEV_CodeFieldRaw.aspis_core.field.QM31 :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromCtorE (e : NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact) : E :=
 ⟨⟨⟨e.c0.c0.a,e.c0.c0.b⟩,⟨e.c0.c1.a,e.c0.c1.b⟩⟩,
  ⟨⟨e.c1.c0.a,e.c1.c0.b⟩,⟨e.c1.c1.a,e.c1.c1.b⟩⟩⟩
def toNativeQ (q : Q) : FIo_Native.aspis_core.field.QM31 :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def fromNativeQ (q : FIo_Native.aspis_core.field.QM31) : Q :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def toNativeE (e : E) : FIo_Native.aspis_core.field.wide_exact.WideExact :=
 ⟨toNativeQ e.c0,toNativeQ e.c1⟩
def fromNativeE (e : FIo_Native.aspis_core.field.wide_exact.WideExact) : E :=
 ⟨fromNativeQ e.c0,fromNativeQ e.c1⟩
def toPushQ (q : Q) : NEI_PushRaw.aspis_core.field.QM31 :=
 ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
end NEV_Bindings

-- Frozen field calls already have direct closed callee bridges. Constructors
-- use the newly emitted normalization path, not an assumed canonical identity.
def aspis_core.field.wide_exact.WideExact.from_qm31 (q : NEV_Bindings.Q) : Result NEV_Bindings.E := do
 let e ← NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.from_qm31 (NEV_Bindings.toCtorQ q)
 ok (NEV_Bindings.fromCtorE e)
def aspis_core.field.wide_exact.WideExact.add (x y : NEV_Bindings.E) : Result NEV_Bindings.E := do
 let e ← FIo_Native.aspis_core.field.wide_exact.WideExact.add (NEV_Bindings.toNativeE x) (NEV_Bindings.toNativeE y)
 ok (NEV_Bindings.fromNativeE e)
def aspis_core.field.wide_exact.WideExact.mul_qm31 (x : NEV_Bindings.E) (y : NEV_Bindings.Q) : Result NEV_Bindings.E := do
 let e ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul_qm31 (NEV_Bindings.toNativeE x) (NEV_Bindings.toNativeQ y)
 ok (NEV_Bindings.fromNativeE e)
def aspis_core.field.M31.ZERO : Result U32 := ok 0#u32
def aspis_core.field.M31.ONE : Result U32 := ok 1#u32
abbrev aspis_core.field.M31.sub := NEI_LineFull.aspis_core.field.M31.sub
abbrev aspis_core.field.M31.mul := NEI_LineFull.aspis_core.field.M31.mul
abbrev aspis_core.field.M31.double := NEI_LineFull.aspis_core.field.M31.double

def aspis_core.field.QM31.mul (x y : NEV_Bindings.Q) : Result NEV_Bindings.Q := do
 let q ← FIo_Native.aspis_core.field.QM31.mul (NEV_Bindings.toNativeQ x) (NEV_Bindings.toNativeQ y)
 ok (NEV_Bindings.fromNativeQ q)
def aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 (x : U32) : Result NEV_Bindings.E := do
 let e ← NEV_CodeFieldRaw.aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31 x
 ok (NEV_Bindings.fromCtorE e)
-- program-build disables the diagnostic trace body. This is source parity,
-- not runtime oracle trust or a successful-result premise.
def trace.value (_ : U16) (_ : Usize) (_ : NEV_Bindings.E) : Result Unit := ok ()
def BatchedWeights.push (b : BatchedWeights) (j : Usize) (q : NEV_Bindings.Q) (m : U32) : Result BatchedWeights := do
 let out ← NEI_PushRaw.BatchedWeights.push ⟨b.raw,b.terms⟩ j (NEV_Bindings.toPushQ q) m
 ok ⟨out.raw,out.terms⟩
end NEV_AccumulateRaw
end
