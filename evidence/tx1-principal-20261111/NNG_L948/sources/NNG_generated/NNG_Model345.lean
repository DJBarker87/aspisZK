import NNG_Fold345
import NNG_Caller345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Model345
open RSL
/-- Concrete source-observation interpretation. Actual emitted-parent value
and chronology association remain separate obligations before candidate use. -/
def interpretation (a : TX1_345.Args) (env : Env) :=
 NNG_Phases345.run LIB_Instances.VL LIB_Instances.C (fun _=>true) NNG_Producer328.producer a env

theorem reference : TX1_345.RowSpec_345 LIB_Instances.VL LIB_Instances.P LIB_Instances.C interpretation :=
 NNG_Phases345.reference_packet LIB_Instances.VL LIB_Instances.P LIB_Instances.C
  LIB_S1.validated_public (NNG_P1880Discharge.decoder LIB_Instances.VL rfl) (fun _=>true)
  NNG_Producer328.producer NNG_Candidate328.candidate
#print axioms reference
end AspisR1.NNG_Model345
