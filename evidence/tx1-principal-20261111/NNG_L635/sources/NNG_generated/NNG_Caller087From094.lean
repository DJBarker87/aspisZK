import NNG_Candidate087
import LIB_VLibR4
import Op3I_ParseLaws
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Caller087From094
open Aeneas Aeneas.Std Result RSL

theorem width_of_source (proof : Bytes) (env : Env) (variant : Op3I_Source.transport.Variant)
 (bound : proof.length≤Usize.max)
 (returned : LIBC_ParseShape.model proof env=.ok (.Ok variant)) : proof.length=57607 := by
 have width:=(Op3I_ParseLaws.source_success (LIBC_Bytes.raw proof) variant returned).2.1
 rw [LIBC_Bytes.raw_length proof bound] at width
 exact width
#print axioms width_of_source

/-- This is the caller discharge on the reached arm, not a new094 input
clause. The successful scan and its events refer to the SAME original proof. -/
theorem domain (a : TX1_094.Args LIB_Instances.VL) (env : Env) (ev : List Event)
 (publicDom : LIB_Instances.VL.publicDom a.public_)
 (width : a.proof.length=57607)
 (scan : LIB_Instances.VL.canonicalScan.run a.proof env ⟨.ret (.ok ()),ev⟩) :
 TX1_087.Domain LIB_Instances.VL ⟨a.public_,a.proof,LIB_Instances.VL.zeroE29⟩ none := by
 exact ⟨width,rfl,publicDom,TX1_094.r4_of_scan LIB_Instances.VL LIB_VLibR4.discharge a env ev scan⟩
#print axioms domain

theorem occurrence (a : TX1_094.Args LIB_Instances.VL) (env : Env) (ev : List Event)
 (publicDom : LIB_Instances.VL.publicDom a.public_) (width : a.proof.length=57607)
 (scan : LIB_Instances.VL.canonicalScan.run a.proof env ⟨.ret (.ok ()),ev⟩) :
 Spec.call (fun x : TX1_087.Args LIB_Instances.VL=>TX1_087.Domain LIB_Instances.VL x none)
  (TX1_087.Ref LIB_Instances.VL LIB_Instances.P) ⟨a.public_,a.proof,LIB_Instances.VL.zeroE29⟩ env
  (NNG_Producer087.producer ⟨a.public_,a.proof,LIB_Instances.VL.zeroE29⟩ none env) := by
 have caller:=domain a env ev publicDom width scan
 exact ⟨caller,NNG_Candidate087.candidate _ none env caller⟩
#print axioms occurrence
end AspisR1.NNG_Caller087From094
