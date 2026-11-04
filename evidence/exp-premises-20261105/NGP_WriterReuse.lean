import NGP_L159
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGP_WriterReuse
open Aeneas Aeneas.Std
/-- The KNE writer identity is already proved on its exact domain. This proves
only Writer_statement; native TX1:186 and the producer domain remain OPEN. -/
theorem writer_model (p : AspisR1.CheckpointBytes5Writer.Prepared)
    (a : AspisR1.CheckpointBytes5Writer.Accumulator)
    (domain : AspisR1.NGC_KNE_Caller.WriterDomain p a) (proof public1 : Slice U8) :
    AspisR1.NGP_L159.Writer_statement p a domain proof public1 :=
  AspisR1.NGC_KNE_Writer.cohort_program_eq p a domain proof public1
#print axioms writer_model
end AspisR1.NGP_WriterReuse
