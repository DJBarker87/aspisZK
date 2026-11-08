import NMX_R4_CallLaws
set_option autoImplicit false
noncomputable section
namespace NMX_R4_TryObservation
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_R4_CallProgram NMX_R4_CallRun

def after {A : Type} (r : core.result.Result A PE)
 (k : A → Program (core.result.Result Auth PE)) : Program (core.result.Result Auth PE) := do
 let cf ← scalar (core.result.Result.Insts.CoreOpsTry.branch r)
 match cf with
 | .Continue a => k a
 | .Break residual =>
   scalar (core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
     Auth (core.convert.FromSame PE) residual)

theorem error (c : Context) {A : Type} (e : PE)
 (k : A → Program (core.result.Result Auth PE)) :
 observe c (after (.Err e) k) = ⟨.ret (.error (NMX_R2_Carrier.error e)),[]⟩ := rfl

theorem success (c : Context) {A : Type} (a : A)
 (k : A → Program (core.result.Result Auth PE)) :
 observe c (after (.Ok a) k) = observe c (k a) := rfl

theorem native (c : Context) {A : Type} (o : RSL.Obs (Except RSL.ProgramError A))
 (k : A → Program (core.result.Result Auth PE)) :
 NMX_R2_Observation.bind (map nativeReply o) (fun r => observe c (after r k)) =
 NMX_R2_Observation.rustBind o (fun a => observe c (k a)) := by
 cases o with
 | mk exit events =>
  cases exit with
  | abort => rfl
  | diverge => rfl
  | ret r =>
   cases r with
   | ok a => rfl
   | error e =>
     simp only [map,nativeReply,NMX_R2_Observation.bind,error,
       NMX_R2_ErrorModelInverse.error,NMX_R2_Observation.rustBind,List.append_nil]

theorem child (c : Context) {A : Type} (cmd : NMX_Program.Command A)
 (k : A → Program (core.result.Result Auth PE)) :
 observe c (NMX_R4_CallProgram.bind (NMX_R4_CallProgram.child cmd) (fun r => after r k)) =
 NMX_R2_Observation.rustBind
  (NMX_R2_NativeExecution.command c.owners c.allocations c.failure c.lane c.registry c.env cmd)
  (fun a => observe c (k a)) := by
 rw [NMX_R4_CallLaws.observed_bind,NMX_R4_CallLaws.run_child,native,native_command]

#print axioms error
#print axioms success
#print axioms native
#print axioms child
end NMX_R4_TryObservation
end
