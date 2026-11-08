import NMS_R2Replay241
set_option autoImplicit false
namespace NMX_R7_RelVerify241
open RSL RSL.TX2_241 NMS_R2Refine NMS_R2Replay241
abbrev VerifyRelation (V : V2Lib) := VerifyArgs → Spec (Except V.VErr Unit)
def RelPacket (V : V2Lib) (verify : VerifyRelation V) : Prop :=
 ∀ x, Dom064 V x → Refines (verify x) (V.tx2auth x.1 x.2.1 x.2.2)

theorem call (V : V2Lib) (verify : VerifyRelation V) (packet : RelPacket V verify)
 (x : VerifyArgs) (domain : Dom064 V x) :
 Refines (verify x) (Spec.call (Dom064 V) (fun x => V.tx2auth x.1 x.2.1 x.2.2) x) :=
 fun env o run => ⟨domain,packet x domain env o run⟩
#print axioms call
end NMX_R7_RelVerify241
