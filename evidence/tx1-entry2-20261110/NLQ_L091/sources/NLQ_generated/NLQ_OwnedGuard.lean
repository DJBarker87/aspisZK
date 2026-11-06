import NLQ_EmissionGuard
set_option autoImplicit false
noncomputable section
namespace NLQ_OwnedGuard
open Aeneas Aeneas.Std Result AspisR1
/-- The instruction comparison precedes EVERY account use. Both TX1 tags
are retained, including the eleven path's possible earlier account errors. -/
theorem ten_wrong_count (ops : AdapterRw.Ops) (p : AdapterRw.solana_pubkey.Pubkey)
 (accounts : Slice AdapterRw.r1_pool_adapter.owned.OwnedAccount)
 (bad : Slice.len accounts≠3#usize) :
 NLD_Stage1Source.stage1Owned (NLQ_EmissionGuard.installed ops) p accounts NJD_Prefixes.ten =
 ([2863],.ok (.Err AdapterRw.solana_program_error.ProgramError.InvalidInstructionData)) := by
 have h10 : (NLQ_EmissionGuard.installed ops).op1 core.cmp.PartialEqU8 NJD_Prefixes.ten
  (Array.make 2#usize [3#u8,10#u8])=.ok true := by
  simp [NLQ_EmissionGuard.installed,NLQ_EmissionGuard.equality,NGL_ReadonlyModel.install,
   NJD_Prefixes.ten,Array.make]
 unfold NLD_Stage1Source.stage1Owned
 simp [NLD_SourceTrace.call,NJD_Trace.call,Bind.bind,NJD_Trace.bind,h10,bad,NJD_Trace.pure]
#check @ten_wrong_count
#print axioms ten_wrong_count
end NLQ_OwnedGuard
