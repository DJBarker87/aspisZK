import NLQ_SourceDispatch
set_option autoImplicit false
noncomputable section
namespace NLQ_DispatchState
open Aeneas Aeneas.Std Result AspisR1
abbrev Reply := core.result.Result Unit Hiq_DispatchSource.PE
/-- Full child footprint, including its actual post-state on abort. -/
structure Child (F C : Type) where
 result : Result Reply
 post : F
 events : List C
abbrev Call (A F C : Type) := Hiq_DispatchSource.Key → Slice A → Slice U8 → F → Child F C
structure Children (A F C : Type) where
 first : Call A F C
 second : Call A F C
 init : Call A F C
 write : Call A F C
 finalize : Call A F C
/-- One event type per dispatch parent. Account carriers and world are exact;
no identity of payloads is inferred from an address comparison. -/
inductive Event (A F C : Type) where
 | head (state : F) (data : Slice U8) (reply : Result (Option U8))
 | copied (state : F) (value : Option U8) (reply : Result (Option U8))
 | eq (state : F) (data : Slice U8) (expected : Array U8 2#usize) (reply : Result Bool)
 | admitted (state : F) (data : Slice U8) (reply : Result Bool)
 | invoke (before after : F) (program : Hiq_DispatchSource.Key) (accounts : Slice A)
   (data : Slice U8) (reply : Result Reply) (events : List C)
structure Run (A F C : Type) where
 result : Result Reply
 post : F
 events : List (Event A F C)
def prepend {A F C : Type} (events : List (Event A F C)) (run : Run A F C) : Run A F C :=
 {run with events:=events++run.events}
def step {A F C X : Type} (world : F) (event : Result X → Event A F C)
 (reply : Result X) (next : X → Run A F C) : Run A F C :=
 match reply with
 | .fail e => ⟨.fail e,world,[event reply]⟩
 | .div => ⟨.div,world,[event reply]⟩
 | .ok x => prepend [event reply] (next x)
def invoke {A F C : Type} (child : Call A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) : Run A F C :=
 let r := child p a d world
 ⟨r.result,r.post,[.invoke world r.post p a d r.result r.events]⟩
def fallback {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) : Run A F C :=
 let ten := Array.make 2#usize [3#u8,10#u8]
 let eleven := Array.make 2#usize [3#u8,11#u8]
 step world (.eq world d ten) (Hiq_DispatchSource.eqU8 d ten) fun yes =>
 if yes then invoke children.first p a d world else
 step world (.eq world d eleven) (Hiq_DispatchSource.eqU8 d eleven) fun yes =>
 if yes then invoke children.first p a d world else invoke children.second p a d world
def process {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) : Run A F C :=
 step world (.head world d) (Hiq_DispatchSource.firstByte d) fun head =>
 step world (.copied world head) (Hiq_DispatchSource.copied head) fun copied =>
 match copied with
 | none => fallback children p a d world
 | some i => match i with
   | 4#uscalar => invoke children.init p a d world
   | 5#uscalar => invoke children.write p a d world
   | 6#uscalar => invoke children.finalize p a d world
   | _ => fallback children p a d world
def entry {A F C : Type} (children : Children A F C) (p : Hiq_DispatchSource.Key)
 (a : Slice A) (d : Slice U8) (world : F) : Run A F C :=
 step world (.admitted world d) (Hiq_DispatchSource.pool_route.admitted d) fun admitted =>
 if admitted then process children p a d world else ⟨.ok (.Err .InvalidInstructionData),world,[]⟩
def asOps {A F C : Type} (children : Children A F C) (world : F) : Hiq_DispatchSource.Ops A :=
 ⟨fun p a d => (children.first p a d world).result,
  fun p a d => (children.second p a d world).result,
  fun p a d => (children.init p a d world).result,
  fun p a d => (children.write p a d world).result,
  fun p a d => (children.finalize p a d world).result⟩
#print process
#print entry
end NLQ_DispatchState
