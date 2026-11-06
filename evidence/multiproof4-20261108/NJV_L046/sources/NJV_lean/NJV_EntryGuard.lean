import NJV_WellInput

set_option autoImplicit false
noncomputable section
namespace NJV_EntryGuard
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef
attribute [local instance] Classical.propDecidable

/-- Exact arbitrary-reply scalar G of NJP_K066/067 after the CLOSED well_formed
reply is installed. This justifies the Guard constructors of the entry cut. -/
theorem same (physical : Slice U8) (s : reference.Scratch) :
 (decide (0<s.n.val) && decide (s.n.val≤16) &&
   decide (AspisR1.OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s)) &&
   decide (physical.val.length%32=0))=decide (NJV_Entry.Guard physical s) := by
 by_cases guard : NJV_Entry.Guard physical s
 · have d := NJV_Entry.guard_domain physical s guard
   simp only [d.1,d.2,guard.1,guard.2,decide_true,Bool.true_and,guard]
 · have no : ¬ (0<s.n.val ∧ s.n.val≤16 ∧
       AspisR1.OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys s) ∧ physical.val.length%32=0) := by
     intro h
     exact guard ⟨h.2.2.1,h.2.2.2⟩
   apply Bool.eq_iff_iff.mpr
   simp only [Bool.and_eq_true,decide_eq_true_eq,guard,false_iff]
   tauto

#print same
#print axioms same
end NJV_EntryGuard
end
