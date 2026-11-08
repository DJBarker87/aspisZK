import NMX_R4_ObsLaws
set_option autoImplicit false
noncomputable section
namespace NMX_R4_CallLaws
open Aeneas Aeneas.Std Result AdapterRw NMX_OwnedPackets NMX_R4_CallProgram NMX_R4_CallRun

theorem run_bind (c : Context) {A B : Type} (p : Program A) (k : A → Program B) :
 run c (NMX_R4_CallProgram.bind p k) = NMX_R2_Observation.bind (run c p) (fun a => run c (k a)) := by
 induction p with
 | ret a => rfl
 | call cmd next ih =>
  simp only [NMX_R4_CallProgram.bind,run,ih]
  exact (NMX_R4_ObsLaws.bind_assoc _ _ _).symm

theorem run_call (c : Context) {A : Type} (cmd : Command A) :
 run c (call cmd) = command c cmd := NMX_R4_ObsLaws.bind_right _

theorem run_scalar (c : Context) {A : Type} (r : Result A) :
 run c (scalar r) = NMX_R3_RegistryRun.scalar r := run_call c _

theorem run_child (c : Context) {A : Type} (cmd : NMX_Program.Command A) :
 run c (child cmd) = map nativeReply (nativeCommand c cmd) := run_call c _

theorem observed_bind (c : Context) {A : Type} (p : Program A)
 (k : A → Program (core.result.Result Auth PE)) :
 observe c (NMX_R4_CallProgram.bind p k) = NMX_R2_Observation.bind (run c p) (fun a => observe c (k a)) := by
 unfold observe
 rw [run_bind,NMX_R4_ObsLaws.map_bind]

theorem observed_scalar (c : Context) {A : Type} (r : Result A)
 (k : A → Program (core.result.Result Auth PE)) :
 observe c (NMX_R4_CallProgram.bind (scalar r) k) =
 NMX_R2_Observation.bind (NMX_R3_RegistryRun.scalar r) (fun a => observe c (k a)) := by
 rw [observed_bind,run_scalar]

#print axioms run_bind
#print axioms run_call
#print axioms run_scalar
#print axioms run_child
#print axioms observed_bind
#print axioms observed_scalar
end NMX_R4_CallLaws
end
