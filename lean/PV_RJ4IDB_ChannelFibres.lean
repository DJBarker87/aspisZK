import PV_RJ4IDB_ResultChannels
set_option autoImplicit false
namespace PV_RJ4IDB
open R1Z.PV_W_Threading R1Z.PV_RJDec_Factor
variable {W A : Type}
/-- One named outstanding law per observed channel, including same-error and
divergent prefixes. This is an OPEN obligation type, not a proved instance. -/
def ChannelLaw (reachable : Run W Event Aeneas.Std.Error A → Prop)
 {V : Type} (project : List Event → V) : Prop :=
 Fibres reachable (fun r => project (r.calls.map Prod.snd))

/-- The already retained complete-Result output components satisfy all fibres. -/
theorem available_result_component {V : Type}
 (reachable : Run W Event Aeneas.Std.Error A → Prop)
 (decode : Aeneas.Std.Result (A × W) → V) :
 Fibres reachable (fun r => decode (R1Z.PV_RunJoin_WorldDecode33.returned r)) :=
 returned_component reachable decode

/-- Event projection composition uses a single coupled event law, so it
cannot manufacture a joint law from marginal timing/count distributions. -/
theorem projection_law {V : Type} (reachable : Run W Event Aeneas.Std.Error A → Prop)
 (project : List Event → V)
 (h : ChannelLaw reachable (fun es => es)) : ChannelLaw reachable project := by
 intro l r hl hr same
 exact congrArg project (h l r hl hr same)

theorem product_law {V U : Type}
 (reachable : Run W Event Aeneas.Std.Error A → Prop)
 (left : List Event → V) (right : List Event → U) :
 ChannelLaw reachable (fun es => (left es,right es)) ↔
 ChannelLaw reachable left ∧ ChannelLaw reachable right :=
 R1Z.PV_RJDec_Factor.pair_iff reachable _ _
#print axioms available_result_component
#print axioms projection_law
#print axioms product_law
end PV_RJ4IDB
