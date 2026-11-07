import NMB_Stage1Source
import NMB_Guard
import NLQ_Route
set_option autoImplicit false
noncomputable section
namespace NMB_Stage1Parent
open Aeneas Aeneas.Std Result AspisR1 NMB_Stage1Source
inductive Event where
 | instruction (state : State) (data : Slice U8) (tag : U8) (reply : Bool)
 | count (state : State) (length : Nat)
 | body (event : NMB_Stage1Source.Event)
structure Run where
 result : Result (core.result.Result Unit PE)
 post : State
 events : List Event
def initial (x : NMB_Input.Input) : State := ⟨NMB_Snapshot.ready x 0 [],none⟩
def count (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (n : Nat) (a0 a1 a2 : Result Unit) : Run :=
 if n=3 then
  let body := NMB_Stage1Source.G x ops p d a0 a1 a2
  ⟨body.result,body.post,.count (initial x) n::body.events.map Event.body⟩
 else ⟨.ok (.Err .InvalidInstructionData),initial x,[.count (initial x) n]⟩
def prepend (events : List Event) (run : Run) : Run := {run with events:=events++run.events}
/-- Whole frozen stage1 transcription, including short-circuit guards before
any descriptor access, with account metadata indexed by occurrence. -/
def G (x : NMB_Input.Input) (ops : AdapterRw.Ops) (p : Key) (d : Slice U8)
 (n : Nat) (a0 a1 a2 : Result Unit) : Run :=
 let ten := decide (d.val=[3#u8,10#u8])
 if ten then prepend [.instruction (initial x) d 10#u8 ten] (count x ops p d n a0 a1 a2)
 else
  let eleven := decide (d.val=[3#u8,11#u8])
  if eleven then prepend [.instruction (initial x) d 10#u8 ten,.instruction (initial x) d 11#u8 eleven]
    (count x ops p d n a0 a1 a2)
  else ⟨.ok (.Err .InvalidInstructionData),initial x,
    [.instruction (initial x) d 10#u8 ten,.instruction (initial x) d 11#u8 eleven]⟩
#print G
end NMB_Stage1Parent
