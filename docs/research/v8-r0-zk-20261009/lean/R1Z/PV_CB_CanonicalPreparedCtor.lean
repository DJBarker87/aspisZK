import R1Z.PV_CB_CanonicalArrays
import R1Z.PV_CB_CanonicalComplex
import R1Z.PV_CB_CanonicalM31Ops
import R1Z.PV_CB_PreparedTotal
set_option autoImplicit false
namespace R1Z.PV_CB_CanonicalPreparedCtor
open Aeneas Aeneas.Std Result
abbrev Q := PV_CB_CanonicalTower.Q
abbrev C := PV_CB_CanonicalComplex.C
abbrev Prepared := PV_CB_PreparedTotal.Prepared
abbrev Part := Array U32 3#usize

def PartValid (part : Part) : Prop := PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid part
def Valid (prepared : Prepared) : Prop := PV_CB_CanonicalArrays.Valid PartValid prepared.components

theorem new_part (value : C) (canonical : PV_CB_CanonicalComplex.Valid value) :
    ∃ part, PV_CB_PreparedTotal.S.newPart () value = ok part ∧ PartValid part := by
  obtain ⟨sum,hsum,vsum⟩ := PV_CB_CanonicalM31Ops.add value.a value.b canonical.1 canonical.2
  refine ⟨Array.make 3#usize [value.a,value.b,sum],?_,?_⟩
  · simp only [PV_CB_PreparedTotal.S.newPart,
      ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call,
      ProverRwP7CurrentBaseBridge.S.add] at hsum ⊢
    simp only [hsum,bind_tc_ok]
  · intro element member
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact canonical.1
    · exact canonical.2
    · exact vsum

theorem new (value : Q) (canonical : PV_CB_CanonicalTower.Valid value) :
    ∃ prepared, PV_CB_PreparedTotal.S.new value = ok prepared ∧ Valid prepared := by
  obtain ⟨p0,h0,v0⟩ := new_part value.c0 canonical.1
  obtain ⟨p1,h1,v1⟩ := new_part value.c1 canonical.2
  obtain ⟨sum,hsum,vsum⟩ := PV_CB_CanonicalComplex.add value.c0 value.c1 canonical.1 canonical.2
  obtain ⟨p2,h2,v2⟩ := new_part sum vsum
  refine ⟨⟨Array.make 3#usize [p0,p1,p2]⟩,?_,?_⟩
  · simp only [PV_CB_PreparedTotal.S.new,
      ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.new,
      PV_CB_CurrentComplex.S.add] at hsum ⊢
    simp only [h0,h1,hsum,h2,bind_tc_ok]
  · intro element member
    simp only [Array.make,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl
    · exact v0
    · exact v1
    · exact v2
#print axioms new_part
#print axioms new
end R1Z.PV_CB_CanonicalPreparedCtor
