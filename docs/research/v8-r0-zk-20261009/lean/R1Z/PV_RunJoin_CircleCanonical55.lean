import R1Z.PV_RunJoin_CircleTotal55
set_option autoImplicit false
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_RunJoin_CircleCanonical55
open PV_RunJoin_CircleR72Carrier52 PV_RunJoin_CircleNeutralShape53
open AspisV8R15.ExactTowerBase
open AspisV8R19.SamplerClosureCircleSourceExecution
open AspisV8R19.SamplerClosureProductCorrectness

theorem decode_canonical (q : OQ) (hc : Canonical q) : QC (decQ q) :=
  ⟨⟨hc.1,hc.2.1⟩,hc.2.2⟩

theorem encoded (p : QM31Exact × QM31Exact) :
    QC (decPoint (encodePoint p)).1 ∧ QC (decPoint (encodePoint p)).2 :=
  ⟨decode_canonical _ (encode_canonical p.1),decode_canonical _ (encode_canonical p.2)⟩

theorem complete (block : Array U8 32#usize) (row : Bool) :
    ∃ p,PV_RunJoin_CircleRawMap52.circle_owned block row=ok p ∧ QC p.1 ∧ QC p.2 :=
  ⟨_,PV_RunJoin_CircleTotal55.complete block row,encoded _⟩
#print axioms decode_canonical
#print axioms encoded
#print axioms complete
end R1Z.PV_RunJoin_CircleCanonical55
