import NLQ_Stage1Fold
import NLQ_Route
set_option autoImplicit false
noncomputable section
namespace NLQ_Stage1Parent
open Aeneas Aeneas.Std Result AspisR1 NLQ_Stage1State
/-- Stage1's own event alphabet includes the short-circuit guard before any
snapshot call. Body events retain the SAME stateful child chain. -/
inductive Event where
 | instruction (state : State) (data : Slice U8) (tag : U8) (reply : Bool)
 | count (state : State) (length : Nat)
 | body (event : NLQ_Stage1State.Event)
structure Run where
 result : Result (core.result.Result Unit PE)
 post : State
 events : List Event
def initial (e : S2W_D189Entry.Entry) : State := ⟨NLM_Snapshot.ready e 0 [],none⟩
def count (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (n : Nat) (a0 a1 a2 : Result Unit) : Run :=
 if n=3 then
  let body := NLQ_Stage1Fold.G e ops p d a0 a1 a2
  ⟨body.result,body.post,.count (initial e) n::body.events.map Event.body⟩
 else ⟨.ok (.Err .InvalidInstructionData),initial e,[.count (initial e) n]⟩
def prepend (events : List Event) (run : Run) : Run := {run with events:=events++run.events}
def G (e : S2W_D189Entry.Entry) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (n : Nat) (a0 a1 a2 : Result Unit) : Run :=
 let ten := decide (d.val=[3#u8,10#u8])
 if ten then prepend [.instruction (initial e) d 10#u8 ten] (count e ops p d n a0 a1 a2)
 else
  let eleven := decide (d.val=[3#u8,11#u8])
  if eleven then prepend [.instruction (initial e) d 10#u8 ten,.instruction (initial e) d 11#u8 eleven]
    (count e ops p d n a0 a1 a2)
  else ⟨.ok (.Err .InvalidInstructionData),initial e,
   [.instruction (initial e) d 10#u8 ten,.instruction (initial e) d 11#u8 eleven]⟩
#print G
end NLQ_Stage1Parent
