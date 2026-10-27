import R1Z.PV_CB3_StagedIndex
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedDecode
open Aeneas Aeneas.Std Result ProverRwFull
open PV_CB3_StagedIndex

def decode (a : Array U32 8#usize) : Result aspis_core.field.wide_exact.WideExact :=
  PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new
    {c0 := {a := limb a ⟨0,by decide⟩,b := limb a ⟨1,by decide⟩},
     c1 := {a := limb a ⟨2,by decide⟩,b := limb a ⟨3,by decide⟩}}
    {c0 := {a := limb a ⟨4,by decide⟩,b := limb a ⟨5,by decide⟩},
     c1 := {a := limb a ⟨6,by decide⟩,b := limb a ⟨7,by decide⟩}}

def suffix (a : Array U32 8#usize) : Result aspis_core.field.wide_exact.WideExact := do
  let i0 ← Array.index_usize a 0#usize
  let i1 ← Array.index_usize a 1#usize
  let i2 ← Array.index_usize a 2#usize
  let i3 ← Array.index_usize a 3#usize
  let i4 ← Array.index_usize a 4#usize
  let i5 ← Array.index_usize a 5#usize
  let i6 ← Array.index_usize a 6#usize
  let i7 ← Array.index_usize a 7#usize
  PV_CB3_StagedFields.aspis_core.field.wide_exact.WideExact.new
    {c0 := {a := i0,b := i1},c1 := {a := i2,b := i3}}
    {c0 := {a := i4,b := i5},c1 := {a := i6,b := i7}}

theorem suffix_eq (a : Array U32 8#usize) : suffix a = decode a := by
  simp only [suffix,decode,bind_tc_ok,read0,read1,read2,read3,read4,read5,read6,read7]

theorem total (a : Array U32 8#usize) : ∃ x, decode a = ok x := by
  exact PV_CB3_StagedTotal.constructor_total _ _
#print axioms suffix_eq
#print axioms total
end R1Z.PV_CB3_StagedDecode
