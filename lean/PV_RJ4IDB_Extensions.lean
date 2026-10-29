import PV_RJ4IDB_DecoderCases
import PV_RJ4IDB_ChannelFibres
set_option autoImplicit false
noncomputable section
namespace PV_RJ4IDB
open Aeneas Aeneas.Std R1Z.PV_W_Threading R1Z.PV_RunJoin_WorldDecode33
variable {W A V : Type}
/-- Existence at the old Result interface requires the exact fibres; the
trace-based native adapter above needs no prefix erasure. No instance is
asserted for file, diagnostic, timing, ROM or retained side channels. -/
theorem result_decoder_exists_iff [Nonempty V]
 (reachable : Run W Event Error A → Prop) (component : List Event → V) :
 (∃ decode : Result (A × W) → V, ∀ r, reachable r →
 decode (returned r)=component (r.calls.map Prod.snd)) ↔ ChannelLaw reachable component :=
 R1Z.PV_RJDec_Factor.exists_iff reachable _

/-- Exact success/failure/divergence obligations for each component. -/
theorem component_cases (reachable : Run W Event Error A → Prop)
 {U : Type} (component : List Event → U) :
 ChannelLaw reachable component ↔
 (∀ l r a, reachable l → reachable r → l.outcome=.ok a → r.outcome=.ok a →
 l.world=r.world → component (l.calls.map Prod.snd)=component (r.calls.map Prod.snd)) ∧
 (∀ l r e, reachable l → reachable r → l.outcome=.fail e → r.outcome=.fail e →
 component (l.calls.map Prod.snd)=component (r.calls.map Prod.snd)) ∧
 (∀ l r, reachable l → reachable r → l.outcome=.div → r.outcome=.div →
 component (l.calls.map Prod.snd)=component (r.calls.map Prod.snd)) :=
 trace_component_fibres reachable component
#print axioms result_decoder_exists_iff
#print axioms component_cases
end PV_RJ4IDB
