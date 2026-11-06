import NKK_RunEval
import NJU_ResumeObserved
set_option autoImplicit false
noncomputable section
namespace NKK_FieldFold
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev Reader := verifier.Reader
abbrev R (A : Type) := Result (core.result.Result A verifier.Error)
inductive Kind where | k | e
inductive Value where
 | k (value : aspis_core.field.QM31)
 | e (value : aspis_core.field.wide_exact.WideExact)

def mapInner {A B : Type} (f : A → B) : core.result.Result A verifier.Error → core.result.Result B verifier.Error
 | .Ok a => .Ok (f a)
 | .Err e => .Err e

def mapOuter {A B : Type} (f : A → B) : Result A → Result B
 | .ok a => .ok (f a)
 | .fail e => .fail e
 | .div => .div

def event (kind : Kind) (r : Reader) : NJU_ResumeObserved.Event :=
 match kind with
 | .k => .k r (NIL_FreshOps.readK r)
 | .e => .e r (NIL_FreshOps.readE r)

def response : NJU_ResumeObserved.Event → Result (core.result.Result Value verifier.Error × Reader)
 | .k _ reply => mapOuter (fun x=>(mapInner Value.k x.1,x.2)) reply
 | .e _ reply => mapOuter (fun x=>(mapInner Value.e x.1,x.2)) reply
 | _ => .fail .panic

/-- One native stage-child event, with its complete actual reply. -/
def call (kind : Kind) (r : Reader) :
 NJU_Log.Run NJU_ResumeObserved.Event (core.result.Result Value verifier.Error × Reader) :=
 ⟨response (event kind r),[event kind r]⟩

def program : List Kind → Reader → NJU_Log.Run NJU_ResumeObserved.Event
 (core.result.Result (List Value × Reader) verifier.Error)
 | [],r => pure (.Ok ([],r))
 | kind::kinds,r => do
   let (reply,next) ← call kind r
   match reply with
   | .Err err => pure (.Err err)
   | .Ok value =>
     let tail ← program kinds next
     pure (mapInner (fun x=>(value::x.1,x.2)) tail)

structure State where
 values : List Value
 reader : Reader
 status : R Unit

def step (s : State) (e : NJU_ResumeObserved.Event) : State :=
 match s.status with
 | .ok (.Ok _) => match response e with
   | .fail err => {s with status:=.fail err}
   | .div => {s with status:=.div}
   | .ok (.Err err,next) => {s with reader:=next,status:=.ok (.Err err)}
   | .ok (.Ok value,next) => ⟨s.values++[value],next,.ok (.Ok ())⟩
 | _ => s

def fold (events : List NJU_ResumeObserved.Event) (s : State) : State := events.foldl step s

def Matches (before : List Value) (state : State) : R (List Value × Reader) → Prop
 | .ok (.Ok (values,last)) => state=⟨before++values,last,.ok (.Ok ())⟩
 | .ok (.Err err) => state.status=.ok (.Err err)
 | .fail err => state.status=.fail err
 | .div => state.status=.div

/-- The source stops at the exact Rust Err event, after carrying its Reader
post-state in the event. No subsequent parser/allocator event is invented. -/
theorem error_prefix (kind : Kind) (kinds : List Kind) (r next : Reader) (err : verifier.Error)
 (reply : response (event kind r)=.ok (.Err err,next)) :
 (program (kind::kinds) r).events=[event kind r] ∧
 (program (kind::kinds) r).result=.ok (.Err err) := by
 simp only [program,NKK_RunEval.bind_eq,NKK_RunEval.pure_eq,NJU_Log.bind,call,reply,List.append_nil]
 exact ⟨True.intro,True.intro⟩

theorem abort_prefix (kind : Kind) (kinds : List Kind) (r : Reader) (err : Error)
 (reply : response (event kind r)=.fail err) :
 (program (kind::kinds) r).events=[event kind r] ∧
 (program (kind::kinds) r).result=.fail err := by
 simp only [program,NKK_RunEval.bind_eq,NJU_Log.bind,call,reply]
 exact ⟨True.intro,True.intro⟩

theorem div_prefix (kind : Kind) (kinds : List Kind) (r : Reader)
 (reply : response (event kind r)=.div) :
 (program (kind::kinds) r).events=[event kind r] ∧
 (program (kind::kinds) r).result=.div := by
 simp only [program,NKK_RunEval.bind_eq,NJU_Log.bind,call,reply]
 exact ⟨True.intro,True.intro⟩

#print axioms error_prefix
#print axioms abort_prefix
#print axioms div_prefix
end NKK_FieldFold
