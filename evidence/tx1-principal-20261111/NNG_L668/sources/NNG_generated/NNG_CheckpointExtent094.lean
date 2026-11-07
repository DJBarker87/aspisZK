import NNG_Context094
import LIBC_F6
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_CheckpointExtent094
open Aeneas Aeneas.Std Result RSL
/-- The currently installed child has no observation at a different extent,
including no allocation-abort observation. -/
theorem no_observation (p : LIB_VCarriers.Prepared) (a : LIB_VCarriers.Acc)
 (proof publicBytes : Bytes) (bad : publicBytes.length≠1880) (env : Env) (o : Obs Bytes) :
 ¬ LIB_Instances.VL.checkpoint.run (p,a,proof,publicBytes) env o := by
 intro h
 exact bad h.1.2.2
#print axioms no_observation
/-- The parent input domain is independent of this separate byte buffer. -/
theorem parent_domain (a : TX1_094.Args LIB_Instances.VL) (obs : Observer)
 (h : TX1_094.Domain LIB_Instances.VL a obs a.public_) (bytes : Bytes) :
 TX1_094.Domain LIB_Instances.VL {a with public_bytes:=bytes} obs a.public_ := h
#print axioms parent_domain
/-- Concrete empty byte argument witnesses the leaf-domain gap for every
Prepared/Accumulator pair, without claiming that pair is reached. -/
theorem empty_no_observation (p : LIB_VCarriers.Prepared) (a : LIB_VCarriers.Acc)
 (proof : Bytes) (env : Env) (o : Obs Bytes) :
 ¬ LIB_Instances.VL.checkpoint.run (p,a,proof,[]) env o :=
 no_observation p a proof [] (by decide) env o
#print axioms empty_no_observation
/-- The retained CLOSED writer correspondence itself accepts arbitrary byte
slices once its actual record-format domain is established. No length clause
is needed by the SAME source program equality. -/
theorem writer_any_bytes (a : LIBC_Checkpoint.Args)
 (d : AspisR1.NGC_KNE_Caller.WriterDomain (LIBC_Checkpoint.prepared a) (LIBC_Checkpoint.accumulator a))
 (stored publicBytes : Slice U8) :
 AspisR1.NGC_KNE_Writer.sourceProgram (LIBC_Checkpoint.prepared a) (LIBC_Checkpoint.accumulator a)
 d stored publicBytes =
 CheckpointBytes5Writer.writer (LIBC_Checkpoint.prepared a) (LIBC_Checkpoint.accumulator a) stored publicBytes :=
 AspisR1.NGC_KNE_Writer.cohort_program_eq _ _ _ _ _
#print axioms writer_any_bytes
end AspisR1.NNG_CheckpointExtent094
