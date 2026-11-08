import LIBB_V2Star
import NMX_R7_RelValidate241
import NMX_R6_Validation
set_option autoImplicit false
noncomputable section
namespace NMX_R8_RelReplay241
open RSL RSL.TX2_241 NMS_R2Refine NMS_R2StepFacts NMS_R2Replay241 NMX_R7_RelVerify241
abbrev L := LIBB_PoolLib.library
abbrev D := LIBB_PoolLib.deployed
abbrev V := LIBB_V2Star.library

def verify : VerifyRelation V := fun x => V.tx2auth x.1 x.2.1 x.2.2

def replay (choices : NMX_R4_Authentication.Choices) (a : Args) : RS Unit :=
 RS.seq (RS.check (a.accounts.length != 7 || decide (a.data.length < 4)
  || a.data.take 4 != REQUEST_MAGIC) .invalidInstructionData) <|
 RS.bind (observed (NMX_R6_Validation.validate choices)
  (⟨a.program_id,a.accounts,a.data,a.current_slot⟩ : TX2_242.Args))
  (NMS_R2Replay241.afterValidate L V verify a)

/-- Same NMS full-source consumer, retaining the complete064 relation rather
than restricting it to one returned graph. Only original241 D1/D2 are assumed. -/
theorem fold (choices : NMX_R4_Authentication.Choices) (a : Args) (domain : Domain V a) :
 Refines (replay choices a) (TX2_241.Ref L D V a) := by
 rw [NMS_R2Replay241.factor]
 unfold replay
 apply rsseq (refl _)
 apply rsbind_using (call TX2_242.Domain (TX2_242.Ref L D) (NMX_R6_Validation.validate choices)
  (NMX_R6_Validation.root choices) _ trivial)
 intro env validated events execution
 have same : (⟨.ret (.ok validated),events⟩ : Obs _) =
  NMX_R6_Validation.validate choices ⟨a.program_id,a.accounts,a.data,a.current_slot⟩ env := execution
 have law := NMX_R6_Validation.root choices ⟨a.program_id,a.accounts,a.data,a.current_slot⟩ env trivial
 rw [←same] at law
 have scope := NMS_R2Facts242.successful L D LIBB_PoolLib.scanner_extent _ env validated events law
 exact (NMX_R7_RelValidate241.fold L V verify (fun _ _ => refl _) a domain validated scope) env
#print axioms fold
end NMX_R8_RelReplay241
end
