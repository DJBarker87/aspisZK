import NMX_R4_TryObservation
set_option autoImplicit false
noncomputable section
namespace NMX_R4_ObservedStep
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_R4_CallProgram NMX_R4_CallRun
abbrev Final := Program (core.result.Result Auth PE)

theorem rust_congr {A B : Type} (o : RSL.Obs (Except RSL.ProgramError A))
 (f g : A → RSL.Obs (Except RSL.ProgramError B)) (h : ∀ a, f a = g a) :
 NMX_R2_Observation.rustBind o f = NMX_R2_Observation.rustBind o g := by
 unfold NMX_R2_Observation.rustBind
 apply NMX_R4_ObsLaws.bind_congr
 intro reply
 cases reply with
 | error e => rfl
 | ok a => exact h a

theorem scalar (c : Context) {A : Type} (r : Result A)
 (k : A → Final) (next : A → NMX_Program.Program Auth)
 (h : ∀ a, observe c (k a) =
  NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env (next a)) :
 observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.scalar r) k) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Program.bind (NMX_SourceProgram.raw r) next) := by
 rw [NMX_R4_CallLaws.observed_scalar]
 cases r with
 | fail e => rfl
 | div => rfl
 | ok a => exact h a

theorem child (c : Context) {A : Type} (cmd : NMX_Program.Command A)
 (k : A → Final) (next : A → NMX_Program.Program Auth)
 (h : ∀ a, observe c (k a) =
  NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env (next a)) :
 observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child cmd) (fun r => NMX_R4_TryObservation.after r k)) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Program.bind (NMX_SourceProgram.call cmd) next) := by
 rw [NMX_R4_TryObservation.child]
 exact rust_congr _ _ _ h

theorem snapshot (c : Context) (payload : Snapshot)
 (k : Box Snapshot → Final) (next : Box Snapshot → NMX_Program.Program Auth)
 (h : ∀ a, observe c (k a) =
  NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env (next a)) :
 observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.snapshot payload) k) =
 NMX_R2_NativeExecution.run c.owners c.allocations c.failure c.lane c.registry c.env
  (NMX_Program.bind (NMX_SourceProgram.call (.snapshot payload)) next) := by
 rw [NMX_R4_CallLaws.observed_bind]
 unfold NMX_R4_CallProgram.snapshot
 rw [NMX_R4_CallLaws.run_call]
 cases flag : c.allocations.snapshot with
 | false =>
   simpa only [command,flag,Bool.false_eq_true,↓reduceIte,NMX_R2_Observation.bind,
    NMX_Program.bind,NMX_SourceProgram.call,NMX_R2_NativeExecution.run,
    NMX_R2_NativeExecution.command,NMX_R2_Observation.rustBind,List.nil_append] using h ⟨c.owners.snapshot,payload⟩
 | true =>
   simp only [command,flag,↓reduceIte,NMX_R2_Observation.bind,
    NMX_Program.bind,NMX_SourceProgram.call,NMX_R2_NativeExecution.run,
    NMX_R2_NativeExecution.command,NMX_R2_Observation.rustBind,List.nil_append]

#print axioms rust_congr
#print axioms scalar
#print axioms child
#print axioms snapshot
end NMX_R4_ObservedStep
end
