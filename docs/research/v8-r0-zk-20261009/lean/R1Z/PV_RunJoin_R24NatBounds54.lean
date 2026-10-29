import R1Z.PV_RunJoin_R24Inputs54
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_R24NatBounds54
open PV_RunJoin_CircleNeutralShape53 PV_RunJoin_R24Inputs54

theorem first (a b : Q) (ha : QC a) (hb : QC b) :
    a.1.2.val*b.1.2.val≤a.1.1.val*b.1.1.val+4611686014132420609 ∧
    v a b≤a.1.1.val*b.1.1.val+4611686014132420609-a.1.2.val*b.1.2.val+2*u a b+3*2147483647 := by
  have h0 := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.1.1 hb.1.1
  have h1 := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.1.2 hb.1.2
  have h2 := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.1.1 hb.1.2
  have h3 := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.1.2 hb.1.1
  have hbound := bounds a b ha hb
  have h := PV_RunJoin_CircleNeutralR24Bounds53.first _ _ _ _ _ _ h0 h1 h2 h3 hbound.1 hbound.2
  exact ⟨h.1,h.2.2.1⟩

theorem third (a b : Q) (ha : QC a) (hb : QC b) :
    a.1.2.val*b.2.2.val≤a.1.1.val*b.2.1.val+a.2.1.val*b.1.1.val+2*4611686014132420609 ∧
    a.2.2.val*b.1.2.val≤a.1.1.val*b.2.1.val+a.2.1.val*b.1.1.val+2*4611686014132420609-a.1.2.val*b.2.2.val := by
  have h0 := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.1.1 hb.2.1
  have h1 := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.2.1 hb.1.1
  have h2 := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.1.2 hb.2.2
  have h3 := PV_RunJoin_CircleNeutralR24Bounds53.product _ _ ha.2.2 hb.1.2
  have h := PV_RunJoin_CircleNeutralR24Bounds53.third _ _ _ _ h0 h1 h2 h3
  exact ⟨h.2.1,h.2.2⟩
#print axioms first
#print axioms third
end R1Z.PV_RunJoin_R24NatBounds54
