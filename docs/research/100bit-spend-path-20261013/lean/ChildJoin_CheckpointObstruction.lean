import S2W_AuthenticatedInputs

/-! The checkpoint stage replacement cannot instantiate an unconstrained header
parser on an opaque adapter child. These obstructions retain actual success. -/
set_option autoImplicit false
namespace AspisR1.ChildJoin_CheckpointObstruction
open Aeneas Aeneas.Std Result
open MultiproofConeCanonical
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open S2W_AuthenticatedInputs

theorem reader_none (ops : AdapterRw.Ops) (H : Bytes → State)
    (pub proof checkpoint : Slice U8)
    (success : ops.op11 (AdapterRw.SolanaDigest.Insts.Aspis_coreDigestDigest32 ops)
      pub proof checkpoint () none = ok (.Ok ())) :
    ¬ CheckpointReaderConeJoin ops (fun _ => none) H pub proof checkpoint := by
  intro join
  have impossible := join.checkedHeader success
  contradiction

theorem writer_none (ops : AdapterRw.Ops) (H : Bytes → State)
    (semantic : Public) (pub proof : Slice U8) (split : Usize)
    (checkpoint : alloc.vec.Vec U8)
    (success : AdapterRw.first_decoded ops semantic pub proof split = ok (.Ok checkpoint)) :
    ¬ CheckpointWriterConeJoin ops (fun _ => none) H semantic pub proof split := by
  intro join
  have impossible := join.header checkpoint success
  contradiction

#print axioms reader_none
#print axioms writer_none
end AspisR1.ChildJoin_CheckpointObstruction
