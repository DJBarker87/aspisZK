import NJV_Entry
import MultiproofConeCountBounds

set_option autoImplicit false
noncomputable section
namespace NJV_UnitDomain
open Aeneas Aeneas.Std Result NJP_DigestCarrier NJP_ScratchCarrier NJP_CohortWrite
open MultiproofConeRef
open AspisR1.OraclePortFrozenOrder AspisR1.MultiproofConePhysicalViews
attribute [local instance] Classical.propDecidable

def keys (s : reference.Scratch) := (live s 0 s.n.val).map Prod.fst

/-- Own multiproof unit domain. The complete padded slot belongs to the caller;
physical is the exact node-count prefix passed to this particular invocation.
No root equality, acceptance, successful-child reply or ghost exporter. -/
structure Domain (physical slot : Slice U8) (s : reference.Scratch) : Prop where
 positive : 0<s.n.val
 batch : s.n.val≤10
 sorted : wellFormed (keys s)
 count : physical.val.length=32*nodeCount 18 (keys s)
 nodePrefix : physical.val=slot.val.take physical.val.length
 padding : ∀ b∈slot.val.drop physical.val.length,b=0#u8
 capacity : physical.val.length≤slot.val.length
 zero : s.«at»=0#usize

theorem key_length (s : reference.Scratch) : (keys s).length=s.n.val := by
 simp [keys,AspisR1.MultiproofConeRootGuard.live_length]

theorem bytes (physical slot : Slice U8) (s : reference.Scratch)
    (domain : Domain physical slot s) : physical.val.length≤9216 := by
 have small : (keys s).length≤16 := by rw [key_length]; have h := domain.batch; omega
 have counted := AspisR1.MultiproofConeCountBounds.eighteen_bound (keys s) small domain.sorted.2.2.1
 rw [AspisR1.MultiproofConeCountLevels.count_eq _ _ domain.sorted.2.2.1] at counted
 rw [domain.count]
 omega

theorem guard (physical slot : Slice U8) (s : reference.Scratch)
    (domain : Domain physical slot s) : NJV_Entry.Guard physical s := by
 refine ⟨domain.sorted,?_⟩
 rw [domain.count]
 omega

/-- Deployed TX2 has up to twelve occupied leaves. This support bound does not
pretend that twelve implies the narrower ten-leaf unit precondition. -/
theorem twelve_size (s : reference.Scratch) (size : s.n.val≤12) : s.n.val≤16 := by omega

#print key_length
#print axioms key_length
#print bytes
#print axioms bytes
#print guard
#print axioms guard
#print twelve_size
#print axioms twelve_size
end NJV_UnitDomain
end
