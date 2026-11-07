import NNG_ParseTail094
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReferenceHead094
open RSL

theorem port : NNG_ProducerFull094.port=NNG_Producer094.port := rfl
#print axioms port

theorem reference (a : NNG_Input094.Args) (obs : Observer) (env : Env) :
 TX1_094.Ref LIB_Instances.VL LIB_Instances.P a =
 RE.seq (RE.check (a.k != SPLIT) LIB_Instances.VL.vParse)
  (NNG_ParseTail094.reference a obs env) := by
 unfold TX1_094.Ref NNG_ParseTail094.reference NNG_ReferenceMatch094.original
 simp only [TX1_094.Ref.match_1,TX1_094.Ref.match_2,
  NNG_ReferenceMatch094.original.match_1,NNG_ReferenceMatch094.original.match_2]
 congr 1 <;> trace_state
#print axioms reference
end AspisR1.NNG_ReferenceHead094
