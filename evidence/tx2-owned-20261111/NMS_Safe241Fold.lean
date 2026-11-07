import NMS_SafePackets
import NMS_RSL241Fold
set_option autoImplicit false
namespace NMS_Safe241Fold
open RSL RSL.TX2_241 NMS_RSLRefine NMS_RSLStepFacts NMS_RSL241Replay NMS_SafePackets
/-- Parametric source-relational 241 fold on exactly D1/D2 plus the recorded
snapshot-error clause. No Root0 fact is added outside Domain241 V a. -/
theorem fold (L : PoolLib) (D : DeployedIds) (V : V2Lib)
 (validate : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L)))
 (child242 : RowSpec242 L D validate) (scan : NMS_RSL242Facts.ScannerExtent L)
 (verify : VerifyNative V) (child064 : VerifyPacket V verify)
 (a : Args) (domain : Domain241 V a) :
 Refines (replay L V validate verify a) (Ref L D V a) := by
 rw [NMS_RSL241Replay.factor]
 unfold replay
 apply rsseq (refl _)
 apply rsbind_using
 · intro env o run
   exact ⟨trivial,by rw [run]; exact child242 _ env domain.2⟩
 · intro env validated events hvalidate
   have law := child242 ⟨a.program_id,a.accounts,a.data,a.current_slot⟩ env domain.2
   rw [←hvalidate] at law
   have scope := NMS_RSL242Facts.successful L D scan _ env validated events law
   exact (NMS_RSL241Validate.fold L V verify child064 a domain.1 validated scope) env
#print axioms fold
end NMS_Safe241Fold
