import PV_L1C_Prefix
/-! Split the LOSSLESS trace into its timing slots/context and actual serialized
values. Slots and failure tags remain; this is not constant-time execution. -/
set_option autoImplicit false
namespace PV_L1C
open PV_RJ4IDB

def timingSlot : NativeEvent → NativeEvent
 | .wall _ => .wall []
 | e => e

def restoreTimes : List NativeEvent → List Bytes → Option (List NativeEvent × List Bytes)
 | [],ts => some ([],ts)
 | .wall _ :: es,[] => none
 | .wall _ :: es,t::ts => (restoreTimes es ts).map (fun p => (.wall t::p.1,p.2))
 | e::es,ts => (restoreTimes es ts).map (fun p => (e::p.1,p.2))

theorem restore_times (es : List NativeEvent) (tail : List Bytes) :
 restoreTimes (es.map timingSlot) (nativeTimes es ++ tail) = some (es,tail) := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   cases e <;> simp only [List.map_cons,timingSlot,nativeTimes,List.filterMap_cons,
     List.cons_append,List.nil_append,restoreTimes,ih,Option.map_some]

def timingKey {A : Type} (t : NativeTrace A) :
 (List NativeEvent × Terminal A) × List Bytes :=
 ((t.events.map timingSlot,t.terminal),nativeTimes t.events)

/-- Counts, oracle, allocation/address/physical/durable/environment events and
cross-channel order stay in the context. No success conditioning occurs. -/
theorem timing_key_injective {A : Type} : Function.Injective (@timingKey A) := by
 intro l r h
 have hs := congrArg (fun p => p.1.1) h
 have ht := congrArg (fun p => p.1.2) h
 have hw := congrArg Prod.snd h
 have hl := restore_times l.events []
 have hr := restore_times r.events []
 have he : l.events = r.events := by
   have hx : some (l.events,([] : List Bytes)) = some (r.events,[]) := by
     rw [← hl,← hr]
     change restoreTimes (l.events.map timingSlot) (nativeTimes l.events ++ []) =
       restoreTimes (r.events.map timingSlot) (nativeTimes r.events ++ [])
     rw [show l.events.map timingSlot = r.events.map timingSlot from hs,
       show nativeTimes l.events = nativeTimes r.events from hw]
   exact congrArg Prod.fst (Option.some.inj hx)
 cases l; cases r; cases he; cases ht; rfl

#print axioms restore_times
#print axioms timing_key_injective
end PV_L1C
