import PV_RJ4IDB_Decoder
import R1Z.PV_RJDec_ResultCases
set_option autoImplicit false
namespace PV_RJ4IDB
open R1Z.PV_W_Threading
variable {W A : Type}
def outcomeTerminal (render : Aeneas.Std.Error → Bytes) :
 Outcome Aeneas.Std.Error A → Terminal A
 | .ok a => .success a
 | .fail e => .failure (render e)
 | .div => .diverge
/-- Each source call is already a full visible event, recorded at its own world.
The trace does not discard rejected-call prefixes or terminal failure prefixes. -/
def sourceTrace (render : Aeneas.Std.Error → Bytes)
 (r : Run W Event Aeneas.Std.Error A) : Trace A :=
 ⟨r.calls.map Prod.snd,outcomeTerminal render r.outcome⟩

def actualObservation (render : Aeneas.Std.Error → Bytes)
 (r : Run W Event Aeneas.Std.Error A) : Observation A :=
 ⟨r.calls.map Prod.snd,outcomeTerminal render r.outcome,
 files (r.calls.map Prod.snd),json (r.calls.map Prod.snd),stdout (r.calls.map Prod.snd),
 diagnostics2 (r.calls.map Prod.snd),diagnostics3 (r.calls.map Prod.snd),
 counts (r.calls.map Prod.snd),times (r.calls.map Prod.snd),
 oracle (r.calls.map Prod.snd),rejections (r.calls.map Prod.snd),sideChannels (r.calls.map Prod.snd)⟩
/-- Exact factorization for the event-interpreted source carrier, on every
reachable path and every finite divergent prefix. Native trace association is
an owning-line input, never an assumption that this conclusion holds. -/
theorem actual_factors (render : Aeneas.Std.Error → Bytes)
 (r : Run W Event Aeneas.Std.Error A) :
 actualObservation render r = decoder (sourceTrace render r) := rfl

theorem result_fibres_exact (reachable : Run W Event Aeneas.Std.Error A → Prop)
 (render : Aeneas.Std.Error → Bytes) :
 R1Z.PV_RJDec_Factor.Fibres reachable (actualObservation render) ↔
 (∀ l r a, reachable l → reachable r → l.outcome=.ok a → r.outcome=.ok a →
 l.world=r.world → l.calls.map Prod.snd=r.calls.map Prod.snd) ∧
 (∀ l r e, reachable l → reachable r → l.outcome=.fail e → r.outcome=.fail e →
 l.calls.map Prod.snd=r.calls.map Prod.snd) ∧
 (∀ l r, reachable l → reachable r → l.outcome=.div → r.outcome=.div →
 l.calls.map Prod.snd=r.calls.map Prod.snd) := by
 rw [R1Z.PV_RJDec_ResultCases.fibres_iff]
 constructor
 · rintro ⟨hs,hf,hd⟩
   exact ⟨fun l r a hl hr hol hor hw => congrArg Observation.ordered (hs l r a hl hr hol hor hw),
    fun l r e hl hr hol hor => congrArg Observation.ordered (hf l r e hl hr hol hor),
    fun l r hl hr hol hor => congrArg Observation.ordered (hd l r hl hr hol hor)⟩
 · rintro ⟨hs,hf,hd⟩
   refine ⟨?_,?_,?_⟩
   · intro l r a hl hr hol hor hw
     have he := hs l r a hl hr hol hor hw
     simp only [actualObservation,hol,hor,he]
   · intro l r e hl hr hol hor
     have he := hf l r e hl hr hol hor
     simp only [actualObservation,hol,hor,he]
   · intro l r hl hr hol hor
     have he := hd l r hl hr hol hor
     simp only [actualObservation,hol,hor,he]
#print axioms actual_factors
#print axioms result_fibres_exact
end PV_RJ4IDB
