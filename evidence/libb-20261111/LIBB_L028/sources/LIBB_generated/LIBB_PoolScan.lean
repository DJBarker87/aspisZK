import LIBB_ModelGraph
import LIBB_Bytes
import LIBB_PoolCarriers
import NMS_R2N_ScanRegular
import NMS_R2N_ScanScalar
set_option autoImplicit false
noncomputable section
namespace LIBB_PoolScan
open Aeneas Aeneas.Std
abbrev RawReply := core.result.Result AdapterRw.r1_pool_adapter.ScannedAsqaProof AdapterRw.solana_program_error.ProgramError
def reply (r : RawReply) : Except RSL.ProgramError (LIBB_PoolCarriers.Afterstate × Nat) :=
 NMS_R2N_RSLError.reply (fun s => (s.candidate_afterstate,s.proof_length.val)) r
/-- The CLOSED scanner's explicit source model, with its sole Box allocation
at the actual source point after successful decode. No Cut/Windows image. -/
def scanProof (data : RSL.Bytes) : RSL.RS (LIBB_PoolCarriers.Afterstate × Nat) :=
 if bound : data.length ≤ Usize.max then
  RSL.Spec.map reply (NMS_R2N_ScanSites.interpreted (LIBB_Bytes.fromBytes data bound))
 else RSL.Spec.panic

def evaluator (data : RSL.Bytes) : Except RSL.ProgramError (LIBB_PoolCarriers.Afterstate × Nat) :=
 if bound : data.length ≤ Usize.max then
  reply (LIBB_ModelGraph.value (.Err .InvalidAccountData)
   (AspisR1.NFY_JHf_Scan.source (LIBB_Bytes.fromBytes data bound)))
 else .error .invalidAccountData

theorem same_input (b : Slice U8) :
 scanProof (LIBB_Bytes.bytes b) = RSL.Spec.map reply (NMS_R2N_ScanSites.interpreted b) := by
 unfold scanProof
 rw [dif_pos (LIBB_Bytes.bytes_bound b),LIBB_Bytes.from_bytes]

/-- The deterministic returned graph is the supplying root's SAME-input
source value. Allocation stops are retained in scanProof, not chosen away. -/
theorem source_returns (b : Slice U8) (env : RSL.Env) :
 NND_Returned.Returns (NMS_R2N_ScanSites.interpreted b) env
  (LIBB_ModelGraph.value (.Err .InvalidAccountData) (AspisR1.NFY_JHf_Scan.source b)) :=
 LIBB_ModelGraph.returned _ _ _ (fun e r events run =>
  NMS_R2N_ScanRegular.source_return b e r events run) env

theorem returns (data : RSL.Bytes) (env : RSL.Env) :
 NND_Returned.Returns (scanProof data) env (evaluator data) := by
 unfold scanProof evaluator
 split
 · exact NND_Returned.map _ reply env _ (source_returns _ env)
 · exact NND_Returned.panic env _

/-- Representation bridge only; separate from the model's definition. -/
theorem native_copy (b : Slice U8) :
 NMS_R2N_Interpreted.Simulates reply (NMS_R2N_ScanSites.interpreted b)
  (scanProof (LIBB_Bytes.bytes b)) := by
 rw [same_input]
 exact LIBB_ModelGraph.mapped_member _ _
#print axioms same_input
#print axioms source_returns
#print axioms returns
#print axioms native_copy
end LIBB_PoolScan
end
