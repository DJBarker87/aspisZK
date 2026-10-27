import R1Z.PV_CB3_NormalizeIdentity
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB3_StagedUnpack
open Aeneas Aeneas.Std Result ProverRwFull
open PV_CB3_StagedIndex

def raw (a : Array U32 8#usize) : aspis_core.field.wide_exact.WideExact :=
  { c0 := {c0 := {a := limb a ⟨0,by decide⟩,b := limb a ⟨1,by decide⟩},
           c1 := {a := limb a ⟨2,by decide⟩,b := limb a ⟨3,by decide⟩}},
    c1 := {c0 := {a := limb a ⟨4,by decide⟩,b := limb a ⟨5,by decide⟩},
           c1 := {a := limb a ⟨6,by decide⟩,b := limb a ⟨7,by decide⟩}} }

theorem limb_mem (a : Array U32 8#usize) (i : Fin 8) : limb a i ∈ a.val := by
  exact List.getElem_mem (by rw [a.property]; exact i.isLt)

theorem source (a : Array U32 8#usize)
    (canonical : ∀ d, d ∈ a.val → d.val < 2147483647) :
    PV_CB3_StagedDecode.decode a = ok (raw a) := by
  have hc (i : Fin 8) := canonical (limb a i) (limb_mem a i)
  have hl : PV_CB3_NormalizeIdentity.Canonical (raw a).c0 :=
    ⟨⟨hc ⟨0,by decide⟩,hc ⟨1,by decide⟩⟩,⟨hc ⟨2,by decide⟩,hc ⟨3,by decide⟩⟩⟩
  have hr : PV_CB3_NormalizeIdentity.Canonical (raw a).c1 :=
    ⟨⟨hc ⟨4,by decide⟩,hc ⟨5,by decide⟩⟩,⟨hc ⟨6,by decide⟩,hc ⟨7,by decide⟩⟩⟩
  change (do
    let left ← PV_CB3_StagedFields.aspis_core.field.wide_exact.canonical_qm31 (raw a).c0
    let right ← PV_CB3_StagedFields.aspis_core.field.wide_exact.canonical_qm31 (raw a).c1
    ok ({c0 := left,c1 := right} : aspis_core.field.wide_exact.WideExact)) = _
  rw [PV_CB3_NormalizeIdentity.source _ hl,PV_CB3_NormalizeIdentity.source _ hr]
  rfl

def values (x : aspis_core.field.wide_exact.WideExact) : List Nat :=
  [x.c0.c0.a.val,x.c0.c0.b.val,x.c0.c1.a.val,x.c0.c1.b.val,
   x.c1.c0.a.val,x.c1.c0.b.val,x.c1.c1.a.val,x.c1.c1.b.val]

theorem raw_values (a : Array U32 8#usize) : values (raw a) = a.val.map UScalar.val := by
  obtain ⟨a0,a1,a2,a3,a4,a5,a6,a7,h⟩ := PV_CB3_ArrayEight.view a
  subst a
  rfl
#print axioms limb_mem
#print axioms source
#print axioms raw_values
end R1Z.PV_CB3_StagedUnpack
