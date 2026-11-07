import NNH_EnvUnique
import NNH_Libraries
import LIBB_CommonReservation
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNH_064Reservation
open Aeneas Aeneas.Std RSL
/-- The actual runtime tag follows from rev3 EnvRep. Err payloads are retained
in the runtime binder and are never required to equal the canonical payload. -/
theorem tag (sha : List RSL.Bytes → B32) (pda : List RSL.Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : Env) (rep : NNH_HostEnv.EnvRep sha pda clock r env) :
 NJC_FilledClause.reserved r=env.reservation := by
 have h := rep.2.2.2
 cases r with
 | Ok u => cases u; exact (h.mpr rfl).symm
 | Err e =>
  cases b : env.reservation
  · rfl
  · have impossible := h.mp b
    cases impossible

theorem canonical_tag (sha : List RSL.Bytes → B32) (pda : List RSL.Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : Env) (rep : NNH_HostEnv.EnvRep sha pda clock r env) :
 NJC_FilledClause.reserved r=NJC_FilledClause.reserved (LIBB_Tx2Reservation.reservation env) :=
 (tag sha pda clock r env rep).trans (LIBB_Tx2Reservation.reserved env).symm

/-- Full source Result at the actual reservation binder, both success and
failure. This discharges the reservation port, not the missing native record
execution producer for the common arm. -/
theorem common (sha : List RSL.Bytes → B32) (pda : List RSL.Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : Env) (rep : NNH_HostEnv.EnvRep sha pda clock r env) (pub proof ck : Slice U8) :
 NJJ_Common.run r r (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
  (NLB_Parent.finish r) (LIBB_PartitionEnv.digest env) pub proof ck () none =
 LIBB_Tx2EnvCode.common env pub proof ck := by
 have h := canonical_tag sha pda clock r env rep
 unfold LIBB_Tx2EnvCode.common
 rw [LIBB_CommonReservation.source r _ r _ r _
  (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env)) h h h]

/-- Same source event sequence, not merely equality of returned values. -/
theorem observed (sha : List RSL.Bytes → B32) (pda : List RSL.Bytes → B32 → Option B32)
 (clock : Except ProgramError UInt64) (r : NP6_StdModel.Reservation)
 (env : Env) (rep : NNH_HostEnv.EnvRep sha pda clock r env) (pub proof ck : Slice U8) :
 NJU_CommonObserved.run r r (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env))
  (NLB_Parent.finish r) (LIBB_PartitionEnv.digest env) pub proof ck () none =
 LIBB_Tx2EnvCode.observed env pub proof ck := by
 have h := canonical_tag sha pda clock r env rep
 unfold LIBB_Tx2EnvCode.observed
 rw [LIBB_CommonReservation.observed r _ r _ r _
  (NLP_NativeMerkle.action (LIBB_PartitionEnv.H env)) h h h]

#print axioms tag
#print axioms canonical_tag
#print axioms common
#print axioms observed
end AspisR1.NNH_064Reservation
