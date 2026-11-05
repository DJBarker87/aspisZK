import NHL_Tx1Stages
import RPz7_Op4P_Install
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIF_ScanEntry
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NHL_Tx1Stages
open Port3_PushFrame (bind_success)
/-- Entry into THIS TX1 query continuation implies the earlier SAME-proof scan
returned successfully. No query or decoder success premise is introduced. -/
theorem reached_scan (ops : Ops) {H : Type} (prepareCall : NHL_EmittedTx1.Prepare H)
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (public_bytes proof : Slice U8) (k : Usize) (hash : H) (c : Context)
 (run : beforeQuery ops prepareCall D pub public_bytes proof k hash none=ok (.Ok c)) :
 ops.op4 proof=ok (.Ok ()) := by
 unfold beforeQuery at run
 split at run
 · cases run
 · obtain ⟨shape,hs,run⟩ := bind_success _ _ _ run
   cases shape with
   | Err e => cases run
   | Ok variant =>
     simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
     obtain ⟨scan,hscan,run⟩ := bind_success _ _ _ run
     cases scan with
     | Err e => cases run
     | Ok unit => cases unit;exact hscan
#print axioms reached_scan
end AspisR1.NIF_ScanEntry
