import R1Z.PV_RunJoin_CircleNeutralR24Bounds53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24Inputs54
open PV_RunJoin_CircleNeutralShape53
abbrev Q := (U32 × U32) × (U32 × U32)
def u (a b : Q) := AspisV8R19.PartialProduct.foldOnce
  (a.2.1.val*b.2.1.val+4611686014132420609-a.2.2.val*b.2.2.val)
def v (a b : Q) := AspisV8R19.PartialProduct.foldOnce
  (a.2.1.val*b.2.2.val+a.2.2.val*b.2.1.val)
theorem bounds (a b : Q) (ha : QC a) (hb : QC b) : u a b<6442450941 ∧ v a b<6442450941 := by
  have hcg := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.2.1 hb.2.1
  have hdh := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.2.2 hb.2.2
  have hch := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.2.1 hb.2.2
  have hdg := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.2.2 hb.2.1
  have hbound := PV_RunJoin_CircleNeutralR24Bounds53.intermediate _ _ _ _ hcg hdh hch hdg
  exact ⟨AspisV8R19.PartialProduct.partial_bound _ hbound.2.2.1,
    AspisV8R19.PartialProduct.partial_bound _ hbound.2.2.2⟩
#print axioms u
#print axioms v
#print axioms bounds
end R1Z.PV_RunJoin_R24Inputs54
