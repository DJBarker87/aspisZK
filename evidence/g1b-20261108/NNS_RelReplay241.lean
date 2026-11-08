import NNS_Fold241
set_option autoImplicit false
noncomputable section
namespace NNS_RelReplay241
open RSL RSL.TX2_241 NMS_R2Refine NMS_R2StepFacts NMS_R2Replay241
open NMX_R7_RelVerify241 NNS_Fold241

/-- Full242 replay at an explicitly selected064. This is support only and
is not identified with NMX_R9_RelReplay241.replay. -/
def replay (f : Bytes → Bytes → Bytes → Env → Obs (Except V0.VErr Unit))
 (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (a : Args) : RS Unit :=
 RS.seq (RS.check (a.accounts.length != 7 || decide (a.data.length < 4)
  || a.data.take 4 != REQUEST_MAGIC) .invalidInstructionData) <|
 RS.bind (TX2_242.Ref L D ⟨a.program_id,a.accounts,a.data,a.current_slot⟩)
  (afterValidate L (TAS.lib V0 R0 w) (observed (fun x env => f x.1 x.2.1 x.2.2 env)) a)

theorem fold (f : Bytes → Bytes → Bytes → Env → Obs (Except V0.VErr Unit))
 (R0 : Bytes → Bytes → Prop) (w : Bytes → Bytes → Bytes → Spec (Except V0.VErr Unit))
 (h064 : TAS.Refines064 V0 f R0 w) (a : Args) (domain : Domain (TAS.lib V0 R0 w) a) :
 Refines (replay f R0 w a) (TX2_241.Ref L D (TAS.lib V0 R0 w) a) := by
 rw [NMS_R2Replay241.factor]
 unfold replay
 apply rsseq (refl _)
 apply rsbind_using (fun env o run => ⟨trivial,run⟩)
 intro env validated events execution
 have scope := NMS_R2Facts242.successful L D LIBB_PoolLib.scanner_extent _ env validated events execution
 apply (NMX_R7_RelValidate241.fold L (TAS.lib V0 R0 w) _ ?_ a domain validated scope) env
 intro x dx env' o run
 change o = f x.1 x.2.1 x.2.2 env' at run
 subst o
 exact h064 x env' dx

#print axioms fold
end NNS_RelReplay241
