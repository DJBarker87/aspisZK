import NMX_R8_RelReplay241
set_option autoImplicit false
noncomputable section
namespace NMX_R9_RelReplay241
open RSL RSL.TX2_241 NMS_R2Refine NMS_R2StepFacts NMS_R2Replay241 NMX_R7_RelVerify241
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed
abbrev V := LIBB_V2Star.library

def replay (a : Args) : RS Unit :=
 RS.seq (RS.check (a.accounts.length != 7 || decide (a.data.length < 4)
  || a.data.take 4 != REQUEST_MAGIC) .invalidInstructionData) <|
 RS.bind (TX2_242.Ref L D ⟨a.program_id,a.accounts,a.data,a.current_slot⟩)
  (NMS_R2Replay241.afterValidate L V NMX_R8_RelReplay241.verify a)

/-- NMS whole-result consumer for the full242 source relation. No selection of
that child's std outcomes is made. The original D1/D2 discharge every entered
064 clause at the SAME actual reads. -/
theorem fold (a : Args) (domain : Domain V a) : Refines (replay a) (TX2_241.Ref L D V a) := by
 rw [NMS_R2Replay241.factor]
 unfold replay
 apply rsseq (refl _)
 apply rsbind_using (fun env o run => ⟨trivial,run⟩)
 intro env validated events execution
 have scope := NMS_R2Facts242.successful L D LIBB_PoolLib.scanner_extent _ env validated events execution
 exact (NMX_R7_RelValidate241.fold L V NMX_R8_RelReplay241.verify
  (fun _ _ => refl _) a domain validated scope) env
#print axioms fold
end NMX_R9_RelReplay241
end
