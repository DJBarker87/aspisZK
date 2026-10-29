import R1Z.PV_W_OsFile
set_option autoImplicit false
namespace R1Z.PV_W_RepeatFile
open PV_W_Threading PV_RunJoin_OsWorld PV_W_OsFile
open Aeneas.Std

/-- Representability check for the retained FXIO-1 outcome shape. This is a
finite interpreter model, not a universal exclusive-create or errno law. -/
def request : Request Nat := .open64 [] 0#u32 0#u32

def process : PV_W_Enriched.Process Unit Unit where
  statics := fun _ => none
  atomics := fun _ => 0
  heap := fun _ => none
  threadLocal := fun _ _ => none
  allocator := ()
  volatileWrites := []
  atomicOrder := []
  fences := []
  currentThread := 0
  unwinding := false
  extra := ()

abbrev State := Full Unit Nat Bool Unit Unit Bool Unit Unit

def initial : State := ⟨{
  entropy := fun _ => (fun _ => ⟨0,by decide⟩,none)
  entropyUsed := 0
  files := [⟨request,true⟩,⟨request,false⟩]
  fileUsed := 0
  time := []
  timeUsed := 0
  workers := []
  workerUsed := 0 },false,process⟩

def update : Update Nat Bool Bool Unit Unit := fun _ reply fs p => (reply || fs,p)
def tag : Request Nat → Bool → World Unit Nat Bool Unit Unit → Bool := fun _ reply _ => reply

def middle : State := afterFile update request true initial {initial.os with fileUsed := 1}
def finalState : State := afterFile update request false middle {middle.os with fileUsed := 2}

theorem first_step : fileStep request initial.os = some (true,{initial.os with fileUsed := 1}) :=
  file_at initial.os ⟨request,true⟩ rfl

theorem second_step : fileStep request middle.os = some (false,{middle.os with fileUsed := 2}) :=
  file_at middle.os ⟨request,false⟩ rfl

theorem first_call : file update tag request initial = ⟨.ok true,middle,[(initial,true)]⟩ :=
  file_matched update tag request initial true _ first_step

theorem second_call : file update tag request middle = ⟨.ok false,finalState,[(middle,false)]⟩ :=
  file_matched update tag request middle false _ second_step

def repeated : M State Bool Fault (Bool × Bool) :=
  PV_W_Threading.bind (file update tag request) (fun first =>
    PV_W_Threading.bind (file update tag request) (fun second => PV_W_Threading.lift (.ok (first,second))))

theorem repeated_exact : repeated initial =
    ⟨.ok (true,false),finalState,[(initial,true),(middle,false)]⟩ := by
  simp only [repeated,PV_W_Threading.bind,first_call,second_call,PV_W_Threading.lift,
    List.append_nil,List.cons_append,List.nil_append]

theorem retained_world : finalState.os.fileUsed = 2 ∧ finalState.filesystem = true := ⟨rfl,rfl⟩

#print axioms first_step
#print axioms second_step
#print axioms first_call
#print axioms second_call
#print axioms repeated_exact
#print axioms retained_world
end R1Z.PV_W_RepeatFile
