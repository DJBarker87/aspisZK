import PV_RJ4IDB_SourceTrace
set_option autoImplicit false
namespace PV_RJ4IDB
open R1Z.PV_W_Threading R1Z.PV_RJDec_Factor R1Z.PV_RunJoin_WorldDecode33
variable {W C A V U : Type}
/-- Existing complete-Result components (terminal code, published count and
record fields) factor without making any statement about erased prefixes. -/
theorem returned_component (reachable : Run W C Aeneas.Std.Error A → Prop)
 (decode : Aeneas.Std.Result (A × W) → V) :
 Fibres reachable (fun r => decode (returned r)) := by
 intro l r _ _ same
 exact congrArg decode same

theorem returned_success (decode : Aeneas.Std.Result (A × W) → V)
 (l r : Run W C Aeneas.Std.Error A) (a : A)
 (hl : l.outcome=.ok a) (hr : r.outcome=.ok a) (hw : l.world=r.world) :
 decode (returned l) = decode (returned r) := by simp only [returned,hl,hr,hw]

theorem returned_failure (decode : Aeneas.Std.Result (A × W) → V)
 (l r : Run W C Aeneas.Std.Error A) (e : Aeneas.Std.Error)
 (hl : l.outcome=.fail e) (hr : r.outcome=.fail e) :
 decode (returned l) = decode (returned r) := by simp only [returned,hl,hr]

theorem returned_divergence (decode : Aeneas.Std.Result (A × W) → V)
 (l r : Run W C Aeneas.Std.Error A)
 (hl : l.outcome=.div) (hr : r.outcome=.div) :
 decode (returned l) = decode (returned r) := by simp only [returned,hl,hr]

/-- Prefix equality sufficient and NECESSARY for the full lossless decoder;
this is the exact missing component law, not a native instance. -/
theorem trace_component_fibres (reachable : Run W Event Aeneas.Std.Error A → Prop)
 (project : List Event → V) :
 Fibres reachable (fun r => project (r.calls.map Prod.snd)) ↔
 (∀ l r a, reachable l → reachable r → l.outcome=.ok a → r.outcome=.ok a →
 l.world=r.world → project (l.calls.map Prod.snd)=project (r.calls.map Prod.snd)) ∧
 (∀ l r e, reachable l → reachable r → l.outcome=.fail e → r.outcome=.fail e →
 project (l.calls.map Prod.snd)=project (r.calls.map Prod.snd)) ∧
 (∀ l r, reachable l → reachable r → l.outcome=.div → r.outcome=.div →
 project (l.calls.map Prod.snd)=project (r.calls.map Prod.snd)) :=
 R1Z.PV_RJDec_ResultCases.fibres_iff reachable _
#print axioms returned_component
#print axioms returned_success
#print axioms returned_failure
#print axioms returned_divergence
#print axioms trace_component_fibres
end PV_RJ4IDB
