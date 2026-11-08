import NMX_R7_Error241
import NMX_R6_Observation
import LIBB_PoolEncode
set_option autoImplicit false
noncomputable section
namespace NMX_R7_Encoder241
open Aeneas Aeneas.Std Result AdapterRw NMS_R2N_Interpreted
abbrev RawError := aspis_statement.pool_v1.pair_forest_terminal.PoolV1PairForestTerminalFormatErrorV1
abbrev Bytes1880 := Array U8 1880#usize

/-- Post-map_err source observation. The actual frozen callback forgets the
format-error payload; no successful-encoding premise is made. -/
def reply : core.result.Result Bytes1880 AspisS6OuterNativeInstalled.Error →
 core.result.Result Bytes1880 solana_program_error.ProgramError
 | .Ok bytes => .Ok bytes
 | .Err _ => .Err .InvalidInstructionData

def mapped (s : LIBB_PoolCarriers.Statement) : RSL.Spec
 (core.result.Result Bytes1880 solana_program_error.ProgramError) :=
 RSL.Spec.map reply (liftResult (LIBB_PoolEncode.code s))

theorem callback (r : core.result.Result Bytes1880 RawError) :
 core.result.Result.map_err
  r1_pool_adapter.owned.stage2_owned.closure.Insts.CoreOpsFunctionFnOnceTuplePoolV1PairForestTerminalFormatErrorV1ProgramError
  r () = ok (match r with | .Ok b => .Ok b | .Err _ => .Err .InvalidInstructionData) := by
 cases r <;> rfl

theorem classification (r : core.result.Result Bytes1880 AspisS6OuterNativeInstalled.Error) :
 NMS_R2N_RSLError.reply (fun a : Bytes1880 => NMS_R2N_RSLScalars.bytes a.to_slice) (reply r) =
 (match LIBB_PoolEncode.option r with
 | some bytes => Except.ok bytes
 | none => Except.error RSL.ProgramError.invalidInstructionData) := by
 cases r <;> rfl

/-- Cross-carrier meaning of the complete encoder+constant map_err block;
retains code fail/div and every returned format-error classification. -/
theorem full (s : LIBB_PoolCarriers.Statement) :
 Simulates (NMS_R2N_RSLError.reply (fun a : Bytes1880 => NMS_R2N_RSLScalars.bytes a.to_slice))
  (mapped s)
  (RSL.RS.bind (RSL.RS.lift (LIBB_PoolLib.library.encodeStatement s))
   (fun encoded => RSL.RS.ofOption encoded .invalidInstructionData)) := by
 intro env o run
 rcases run with ⟨r,events,next,first,last,same⟩ | ⟨events,first,same⟩ | ⟨events,first,same⟩
 · subst next
   subst o
   let classified : Except RSL.ProgramError RSL.Bytes := match LIBB_PoolEncode.option r with
    | some bytes => .ok bytes
    | none => .error .invalidInstructionData
   unfold RSL.RS.bind
   apply Or.inl
   refine ⟨Except.ok (LIBB_PoolEncode.option r),events,⟨.ret classified,[]⟩,?_,?_,?_⟩
   · have encoding := LIBB_ModelGraph.mapped_member
       LIBB_PoolEncode.option (liftResult (LIBB_PoolEncode.code s)) env _ first
     exact LIBB_ModelGraph.mapped_member Except.ok _ env _ encoding
   · cases r <;> rfl
   · cases r <;> simp only [mapObs,mapExit,reply,classified,List.append_nil]
     all_goals rfl

 · subst o
   unfold RSL.RS.bind RSL.RS.lift RSL.Spec.map
   exact Or.inr (Or.inl ⟨events,Or.inr (Or.inl ⟨events,Or.inr (Or.inl ⟨events,first,rfl⟩),rfl⟩),rfl⟩)
 · subst o
   unfold RSL.RS.bind RSL.RS.lift RSL.Spec.map
   exact Or.inr (Or.inr ⟨events,Or.inr (Or.inr ⟨events,Or.inr (Or.inr ⟨events,first,rfl⟩),rfl⟩),rfl⟩)

#print axioms callback
#print axioms classification
#print axioms full
end NMX_R7_Encoder241
end
