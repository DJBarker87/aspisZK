import SDX_Join_Field
open Aeneas Aeneas.Std Result ControlFlow Error
open SDX_Join_Release
namespace SDX_Join_FieldExternal
/- Explicit field-for-field carrier conversions to the cohort WideExact.
   Producer source: bridge-tx1-e5c186ba3-20261016/AspisR1PublicPreparation/Types.lean:321.
   No algebraic law or source refinement is assumed here. -/
def oldQ (q : aspis_core.field.QM31) : AspisR1PublicPreparation.aspis_core.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def newQ (q : AspisR1PublicPreparation.aspis_core.field.QM31) : aspis_core.field.QM31 :=
  ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def qzero : aspis_core.field.QM31 := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def qone : aspis_core.field.QM31 := ⟨⟨1#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def qeq (a b : aspis_core.field.QM31) : Bool :=
  a.c0.a == b.c0.a && a.c0.b == b.c0.b && a.c1.a == b.c1.a && a.c1.b == b.c1.b
/- Source canonical_qm31: wide_exact.rs. The input representatives reduce mod P. -/
def canon (q : aspis_core.field.QM31) : Result aspis_core.field.QM31 := do
  let a ← q.c0.a % 2147483647#u32
  let b ← q.c0.b % 2147483647#u32
  let c ← q.c1.a % 2147483647#u32
  let d ← q.c1.b % 2147483647#u32
  ok ⟨⟨a,b⟩,⟨c,d⟩⟩
end SDX_Join_FieldExternal

/- Field arithmetic uses the exact source definitions copied into SDX_Join_Field;
   the copy provenance is recorded in that file. Constants use the required
   monadic external ABI rather than a new opaque constant. -/
def aspis_core.field.P : Result U32 := ok 2147483647#u32
def aspis_core.field.M31.ZERO : Result aspis_core.field.M31 := ok 0#u32
def aspis_core.field.M31.ONE : Result aspis_core.field.M31 := ok 1#u32
def aspis_core.field.M31.Insts.CoreCloneClone.clone (x : aspis_core.field.M31) := ok x
def aspis_core.field.M31.Insts.CoreCmpPartialEqM31.eq (a b : aspis_core.field.M31) := ok (a == b)
def aspis_core.field.M31.sub := SDX_Join_Field.field.M31.sub
def aspis_core.field.M31.mul := SDX_Join_Field.field.M31.mul
def aspis_core.field.M31.reduce_u64 := SDX_Join_Field.field.M31.reduce_u64
def aspis_core.field.M31.double := SDX_Join_Field.field.M31.double
def aspis_core.field.CM31.new (a b : aspis_core.field.M31) : Result aspis_core.field.CM31 := ok ⟨a,b⟩
def aspis_core.field.CM31.mul := SDX_Join_Field.field.CM31.mul
def aspis_core.field.QM31.Insts.CoreCloneClone.clone (x : aspis_core.field.QM31) := ok x
def aspis_core.field.QM31.Insts.CoreCmpPartialEqQM31.ne (a b : aspis_core.field.QM31) := ok (!SDX_Join_FieldExternal.qeq a b)
def aspis_core.field.QM31.ZERO : Result aspis_core.field.QM31 := ok SDX_Join_FieldExternal.qzero
def aspis_core.field.QM31.ONE : Result aspis_core.field.QM31 := ok SDX_Join_FieldExternal.qone
def aspis_core.field.QM31.add := SDX_Join_Field.field.QM31.add
def aspis_core.field.QM31.mul := SDX_Join_Field.field.QM31.mul

open SDX_Join_FieldExternal
abbrev SDX_Join_Wide := aspis_core.field.wide_exact.WideExact
def aspis_core.field.wide_exact.WideExact.ZERO : Result SDX_Join_Wide := ok ⟨oldQ qzero,oldQ qzero⟩
def aspis_core.field.wide_exact.WideExact.ONE : Result SDX_Join_Wide := ok ⟨oldQ qone,oldQ qzero⟩
def aspis_core.field.wide_exact.WideExact.new (a b : aspis_core.field.QM31) : Result SDX_Join_Wide := do
  let a ← canon a
  let b ← canon b
  ok ⟨oldQ a,oldQ b⟩
def aspis_core.field.wide_exact.WideExact.from_qm31 (a : aspis_core.field.QM31) : Result SDX_Join_Wide := do
  aspis_core.field.wide_exact.WideExact.new a qzero
def aspis_core.field.wide_exact.WideExact.Insts.CoreCmpPartialEqWideExact.ne (a b : SDX_Join_Wide) : Result Bool :=
  ok (!(qeq (newQ a.c0) (newQ b.c0) && qeq (newQ a.c1) (newQ b.c1)))
def aspis_core.field.wide_exact.WideExact.add (a b : SDX_Join_Wide) : Result SDX_Join_Wide := do
  let c ← SDX_Join_Field.field.QM31.add (newQ a.c0) (newQ b.c0)
  let d ← SDX_Join_Field.field.QM31.add (newQ a.c1) (newQ b.c1)
  ok ⟨oldQ c,oldQ d⟩
def aspis_core.field.wide_exact.WideExact.sub (a b : SDX_Join_Wide) : Result SDX_Join_Wide := do
  let c ← SDX_Join_Field.field.QM31.sub (newQ a.c0) (newQ b.c0)
  let d ← SDX_Join_Field.field.QM31.sub (newQ a.c1) (newQ b.c1)
  ok ⟨oldQ c,oldQ d⟩
/- wide_exact.rs:112-126: ac,bd,cross and mul_u in the same order.
   Reuses the emitted source arithmetic in SDX_Join_Field, with explicit carriers. -/
def aspis_core.field.wide_exact.WideExact.mul (a b : SDX_Join_Wide) : Result SDX_Join_Wide := do
  let ac ← SDX_Join_Field.field.QM31.mul (newQ a.c0) (newQ b.c0)
  let bd ← SDX_Join_Field.field.QM31.mul (newQ a.c1) (newQ b.c1)
  let aa ← SDX_Join_Field.field.QM31.add (newQ a.c0) (newQ a.c1)
  let bb ← SDX_Join_Field.field.QM31.add (newQ b.c0) (newQ b.c1)
  let cross ← SDX_Join_Field.field.QM31.mul aa bb
  let ubd ← SDX_Join_Field.field.wide_exact.mul_u bd
  let c ← SDX_Join_Field.field.QM31.add ac ubd
  let d ← SDX_Join_Field.field.QM31.sub cross ac
  let d ← SDX_Join_Field.field.QM31.sub d bd
  ok ⟨oldQ c,oldQ d⟩
def aspis_core.field.wide_exact.WideExact.mul_qm31 (a : SDX_Join_Wide) (b : aspis_core.field.QM31) : Result SDX_Join_Wide := do
  let c ← SDX_Join_Field.field.QM31.mul (newQ a.c0) b
  let d ← SDX_Join_Field.field.QM31.mul (newQ a.c1) b
  ok ⟨oldQ c,oldQ d⟩
def aspis_core.field.wide_exact.WideExact.mul_m31 (a : SDX_Join_Wide) (b : aspis_core.field.M31) : Result SDX_Join_Wide := do
  let b : aspis_core.field.QM31 := ⟨⟨b,0#u32⟩,⟨0#u32,0#u32⟩⟩
  aspis_core.field.wide_exact.WideExact.mul_qm31 a b
