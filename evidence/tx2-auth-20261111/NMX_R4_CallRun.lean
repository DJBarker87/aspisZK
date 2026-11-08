import NMX_R4_CallProgram
import NMX_R4_BoxAction
import NMX_R2_ErrorModelInverse
import NMX_R3_RegistryRun
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallRun
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_SourceModel NMX_R4_CallProgram

structure Context where
 owners : Owners
 allocations : NMX_R2_NativeExecution.Allocations
 failure : Error
 lane : NMX_R2_RawChildren.LaneNative
 registry : NMX_R2_RawChildren.RegistryNative
 env : RSL.Env

def map {A B : Type} (f : A → B) (o : RSL.Obs A) : RSL.Obs B :=
 ⟨match o.exit with | .ret a => .ret (f a) | .abort => .abort | .diverge => .diverge,o.events⟩
def nativeReply {A : Type} : Except RSL.ProgramError A → core.result.Result A PE
 | .ok a => .Ok a
 | .error e => .Err (NMX_R2_ErrorInverse.fromError e)

def nativeCommand (c : Context) {A : Type} (cmd : NMX_Program.Command A) :
 RSL.Obs (Except RSL.ProgramError A) :=
 match cmd with
 | .master b => NMX_R2_BoxActionObservation.view (NMX_R4_BoxAction.master c.allocations.master c.owners.master b)
 | .checkpoint b => NMX_R2_BoxActionObservation.view (NMX_R4_BoxAction.checkpoint c.allocations.checkpoint c.owners.checkpoint b)
 | other => NMX_R2_NativeExecution.command c.owners c.allocations c.failure c.lane c.registry c.env other

def command (c : Context) {A : Type} : Command A → RSL.Obs A
 | .scalar r => NMX_R3_RegistryRun.scalar r
 | .child cmd => map nativeReply (nativeCommand c cmd)
 | .pda seeds program =>
   let reply := c.env.pda (seeds.val.map NMX_R2_Carrier.bytes) (NMX_R2_Carrier.key program)
   ⟨.ret (match reply with
     | some k => .Ok (NMX_R2_InverseBytes.fromKey k)
     | none => .Err .InvalidSeeds),
    [.pda (seeds.val.map NMX_R2_Carrier.bytes) (NMX_R2_Carrier.key program) reply]⟩
 | .snapshot payload => if c.allocations.snapshot then ⟨.abort,[]⟩
   else ⟨.ret ⟨c.owners.snapshot,payload⟩,[]⟩

def run (c : Context) {A : Type} : Program A → RSL.Obs A
 | .ret a => ⟨.ret a,[]⟩
 | .call cmd next => NMX_R2_Observation.bind (command c cmd) (fun a => run c (next a))

def observe (c : Context) (p : Program (core.result.Result Auth PE)) :
 RSL.Obs (Except RSL.ProgramError RSL.Authenticated) :=
 map (NMX_R2_Carrier.reply NMX_R2_Carrier.auth) (run c p)

theorem native_command (c : Context) {A : Type} (cmd : NMX_Program.Command A) :
 nativeCommand c cmd =
 NMX_R2_NativeExecution.command c.owners c.allocations c.failure c.lane c.registry c.env cmd := by
 cases cmd <;> try rfl
 · exact NMX_R4_BoxAction.master_source _ _ _
 · exact NMX_R4_BoxAction.checkpoint_source _ _ _

#print axioms native_command
end NMX_R4_CallRun
end
