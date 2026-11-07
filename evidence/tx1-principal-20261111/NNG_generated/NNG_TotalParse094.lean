import NNG_ParseCall094
import NNG_Caller087From094
import LIB_ParseShapeTotal
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TotalParse094
open Aeneas Aeneas.Std Result RSL
/-- Total installed field at the SAME original slice, including wrong lengths. -/
theorem occurrence (env : Env) (proof : Slice U8) :
 LIB_Instances.VL.parseShape.run (LIB_Carriers.bytes proof) env
  (LIB_Carriers.resultObs NNG_ParseCall094.port [] (NNG_ParseCall094.call env proof)) := by
 exact ⟨True.intro,NNG_ParseCall094.graph env proof⟩
#print axioms occurrence
/-- Width is obtained only on the actual successful parse arm. -/
theorem returned_width (proof : Bytes) (env : Env) (ev : List Event)
 (h : LIB_Instances.VL.parseShape.run proof env ⟨.ret (.ok ()),ev⟩) :
 proof.length=57607 := by
 by_contra bad
 have rejected := (LIB_ParseShapeTotal.rejected proof env bad _).mp h
 cases congrArg Obs.exit rejected
#print axioms returned_width
/-- Original094 inputs and the SAME reached parse/scan observations discharge
all087 clauses, including rev3 R4 via r4_of_scan. -/
theorem prepare_domain (a : TX1_094.Args LIB_Instances.VL) (env : Env)
 (ep es : List Event) (pub : LIB_Instances.VL.publicDom a.public_)
 (parsed : LIB_Instances.VL.parseShape.run a.proof env ⟨.ret (.ok ()),ep⟩)
 (scanned : LIB_Instances.VL.canonicalScan.run a.proof env ⟨.ret (.ok ()),es⟩) :
 TX1_087.Domain LIB_Instances.VL ⟨a.public_,a.proof,LIB_Instances.VL.zeroE29⟩ none := by
 exact NNG_Caller087From094.domain a env es pub (returned_width _ _ _ parsed) scanned
#print axioms prepare_domain
end AspisR1.NNG_TotalParse094
