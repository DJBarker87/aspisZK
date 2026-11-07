import NNG_PrepareInput087
import NNG_Candidate137
import NNG_Events087
import NNG_PrepareEmission087
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ObservedInput087
open Aeneas Aeneas.Std Result NMP_prepare NMT_CallTree NNG_Observed136
abbrev Args := NNG_PrepareInput087.Args

def child (a : Args) (v : verifier.View) : NNG_Data137.Args :=
 ⟨a.public_,LIB_Carriers.bytes v.semantic⟩

theorem native_bytes (s : Slice U8) : NNG_Data137.bytes (LIB_Carriers.bytes s)=s := by
 unfold NNG_Data137.bytes
 rw [dif_pos (LIB_Bytes.bytes_bound s)]
 exact LIB_Bytes.from_bytes s (LIB_Bytes.bytes_bound s)

theorem input_exact (a : Args) (v : verifier.View) (obs : RSL.Observer) (env : RSL.Env) :
 NNG_Context137.input (child a v) obs env=
   (⟨NNG_PublicSource137.digest env,NMP_Transport.fromT9 a.public_,v.semantic,(),NNG_Context137.observer obs⟩ : NNG_Context137.Parent Unit) := by
 unfold NNG_Context137.input child
 rw [native_bytes]

theorem domain (a : Args) (v : verifier.View) (obs : RSL.Observer)
 (parent : RSL.TX1_087.Domain LIB_Instances.VL a obs) (size : v.semantic.val.length≤57607) :
 RSL.TX1_137.Domain LIB_Instances.VL (child a v) := by
 refine ⟨parent.2.2.1,?_⟩
 change (LIB_Carriers.bytes v.semantic).length≤57607
 rw [NMS_R2N_RSLScalars.bytes_length]
 exact size

theorem observation (a : Args) (v : verifier.View) (obs : RSL.Observer) (env : RSL.Env) :
 NNG_Observed136.observation (NNG_Output137.decode (child a v) env) (NNG_Events087.events env)
   (invoke "TX1:137/verify_observed" ((NNG_PrepareInput087.input a obs env).publicValue,v.semantic,(),NNG_Context137.observer obs)
    (NMP_Emitted.observed (NNG_PrepareEmission087.calls env) {(NNG_PrepareInput087.input a obs env) with bytes:=v.semantic})) =
 NNG_Producer137.producer (child a v) obs env := by
 unfold NNG_Observed136.observation NNG_Producer137.producer
 rw [NNG_FinishOccurrence137.run_invoke]
 simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,NNG_Events087.observed_call]
 rw [input_exact]
 rfl

theorem occurrence (a : Args) (v : verifier.View) (obs : RSL.Observer) (env : RSL.Env)
 (parent : RSL.TX1_087.Domain LIB_Instances.VL a obs) (size : v.semantic.val.length≤57607) :
 RSL.Spec.call (RSL.TX1_137.Domain LIB_Instances.VL) (RSL.TX1_137.Ref LIB_Instances.VL) (child a v) env
  (NNG_Observed136.observation (NNG_Output137.decode (child a v) env) (NNG_Events087.events env)
   (invoke "TX1:137/verify_observed" ((NNG_PrepareInput087.input a obs env).publicValue,v.semantic,(),NNG_Context137.observer obs)
    (NMP_Emitted.observed (NNG_PrepareEmission087.calls env) {(NNG_PrepareInput087.input a obs env) with bytes:=v.semantic}))) := by
 rw [observation]
 exact ⟨domain a v obs parent size,NNG_Candidate137.candidate _ obs env (domain a v obs parent size)⟩
#print axioms native_bytes
#print axioms input_exact
#print axioms domain
#print axioms observation
#print axioms occurrence
end AspisR1.NNG_ObservedInput087
