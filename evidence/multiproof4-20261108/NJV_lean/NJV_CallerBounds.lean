import NJV_UnitDomain

set_option autoImplicit false
noncomputable section
namespace NJV_CallerBounds
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier
open MultiproofConeRef
open AspisR1.OraclePortFrozenOrder

/-- Both TX1 <=10 and TX2 <=12 derive the SAME 9216-byte gate from their own
counted index set. No persistence/history/acceptance premise and no <=10
strengthening on the TX2 path. -/
theorem from_count (physical : Slice U8) (s : reference.Scratch)
    (well : wellFormed (NJV_UnitDomain.keys s))
    (count : physical.val.length=32*nodeCount 18 (NJV_UnitDomain.keys s)) :
 physical.val.length≤9216 := by
 have bounded := AspisR1.MultiproofConeCountBounds.eighteen_bound
   (NJV_UnitDomain.keys s) well.2.1 well.2.2.1
 rw [AspisR1.MultiproofConeCountLevels.count_eq _ _ well.2.2.1] at bounded
 rw [count]
 omega

/-- The same padded slot's exact prefix, and zero padding, retain their own
identities. These are the caller's original clauses, not extra root premises. -/
theorem unit_clauses (physical slot : Slice U8) (s : reference.Scratch)
    (domain : NJV_UnitDomain.Domain physical slot s) :
 physical.val=slot.val.take (32*nodeCount 18 (NJV_UnitDomain.keys s)) ∧
 (∀ b∈slot.val.drop (32*nodeCount 18 (NJV_UnitDomain.keys s)),b=0#u8) ∧
 s.n.val≤10 ∧ wellFormed (NJV_UnitDomain.keys s) := by
 rw [←domain.count]
 exact ⟨domain.nodePrefix,domain.padding,domain.batch,domain.sorted⟩

#print from_count
#print axioms from_count
#print unit_clauses
#print axioms unit_clauses
end NJV_CallerBounds
end
