import LIBB_ModelGraph
import LIBB_AuthCarrier
import NMS_R2N_ReconstructSites
set_option autoImplicit false
noncomputable section
namespace LIBB_PoolReconstruct
open Aeneas Aeneas.Std
open LIBB_PoolCarriers
abbrev reply := NMS_R2N_RSLError.reply (id : Statement → Statement)
/-- Exact CLOSED reconstruction model on the inverse carrier. Its two Box
sites precede statement validation exactly as the frozen body specifies. -/
def reconstruct (q : Request) (a : RSL.Authenticated) (c : Afterstate) : RSL.RS Statement :=
 match LIBB_AuthCarrier.raw a with
 | none => RSL.Spec.panic
 | some raw => RSL.Spec.map reply (NMS_R2N_ReconstructSites.meaning q raw c)

def evaluator (q : Request) (a : RSL.Authenticated) (c : Afterstate) : Except RSL.ProgramError Statement :=
 match LIBB_AuthCarrier.raw a with
 | none => .error .invalidAccountData
 | some raw => reply (LIBB_ModelGraph.value (.Err .InvalidAccountData)
   (AspisR1.NFY_JHf_ReconstructionSlot.source q raw c))

theorem same_input (q : Request) (a : LIBB_AuthCarrier.Raw) (c : Afterstate) :
 reconstruct q (NND_Carrier.auth a) c =
 RSL.Spec.map reply (NMS_R2N_ReconstructSites.meaning q a c) := by
 unfold reconstruct
 rw [LIBB_AuthCarrier.roundtrip]

theorem source_returns (q : Request) (a : LIBB_AuthCarrier.Raw) (c : Afterstate) (env : RSL.Env) :
 NND_Returned.Returns (NMS_R2N_ReconstructSites.meaning q a c) env
  (LIBB_ModelGraph.value (.Err .InvalidAccountData) (AspisR1.NFY_JHf_ReconstructionSlot.source q a c)) :=
 LIBB_ModelGraph.returned _ _ _ (NMS_R2N_ReconstructSites.regular q a c) env

theorem returns (q : Request) (a : RSL.Authenticated) (c : Afterstate) (env : RSL.Env) :
 NND_Returned.Returns (reconstruct q a c) env (evaluator q a c) := by
 unfold reconstruct evaluator
 cases LIBB_AuthCarrier.raw a with
 | none => exact NND_Returned.panic env _
 | some raw => exact NND_Returned.map _ reply env _ (source_returns q raw c env)

theorem native_copy (q : Request) (a : LIBB_AuthCarrier.Raw) (c : Afterstate) :
 NMS_R2N_Interpreted.Simulates reply (NMS_R2N_ReconstructSites.meaning q a c)
  (reconstruct q (NND_Carrier.auth a) c) := by
 rw [same_input]
 exact LIBB_ModelGraph.mapped_member _ _
#print axioms same_input
#print axioms source_returns
#print axioms returns
#print axioms native_copy
end LIBB_PoolReconstruct
end
