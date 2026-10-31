import R1Z.PV_RDCD4_LazyCell
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_LazyReconstruct
open Aeneas Aeneas.Std Result PV_RDCD4_LazyComponents PV_RDCD4_LazyCell
namespace F
abbrev reduce := PV_RDCD4_FieldSource.aspis_core.field.M31.reduce_u64
abbrev sub := PV_RDCD4_FieldSource.aspis_core.field.M31.sub
abbrev cadd := PV_RDCD4_FieldSource.aspis_core.field.CM31.add
abbrev csub := PV_RDCD4_FieldSource.aspis_core.field.CM31.sub
abbrev mulr := PV_RDCD4_FieldSource.aspis_core.field.mul_by_r
end F
def component (channels : List U64) : Result C := do
  let x0 ← read channels 0
  let m0 ← F.reduce x0
  let x1 ← read channels 1
  let m1 ← F.reduce x1
  let x2 ← read channels 2
  let m2 ← F.reduce x2
  let a ← F.sub m0 m1
  let b ← F.sub m2 m0
  let b ← F.sub b m1
  ok ⟨a,b⟩
def source (sums : Sums) : Result Q := do
  let c0 ← read sums 0
  let m0 ← component c0
  let c1 ← read sums 1
  let m1 ← component c1
  let c2 ← read sums 2
  let m2 ← component c2
  let r ← F.mulr m1
  let c0 ← F.cadd m0 r
  let c1 ← F.csub m2 m0
  let c1 ← F.csub c1 m1
  ok ⟨c0,c1⟩
/-- Fixed public channel indices cannot select an absent slot. -/
theorem channel_bound (i : Nat) (hi : i < 3) : i < ([[0#u64,0#u64,0#u64],
    [0#u64,0#u64,0#u64],[0#u64,0#u64,0#u64]] : Sums).length := by
  simpa only [List.length_cons,List.length_nil] using hi
#print axioms channel_bound
end R1Z.PV_RDCD4_LazyReconstruct
