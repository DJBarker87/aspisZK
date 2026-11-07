import NMS_Clone241Validate
set_option autoImplicit false
namespace NMS_Clone241Fold
open RSL RSL.TX2_241 NMS_RSLRefine NMS_RSLStepFacts NMS_Clone241Replay
/-- Canonical full-result relational parent fold. It is PARAMETRIC in V.
The complete 242 packet and SAME-argument 064 packet discharge all child
clauses internally, given only canonical 241 Domain V a. A native row root
still requires the emitted-body/carrier interpretation of `replay`.
No parent-endpoint premise is exported as a native root. -/
theorem fold (L : PoolLib) (D : DeployedIds) (V : V2Lib)
 (validate : TX2_242.Args → Env → Obs (Except ProgramError (TX2_242.Validated L)))
 (child242 : NMS_ClonePackets.RowSpec242 L D validate)
 (scan : NMS_Clone242Facts.ScannerExtent L)
 (verify : VerifyNative V) (child064 : VerifyPacket V verify)
 (a : Args) (domain : Domain V a) :
 Refines (replay L V validate verify a) (NMS_CloneRef241.Ref L D V a) := by
 rw [factor]
 unfold replay
 apply rsseq (refl _)
 apply rsbind_using (call TX2_242.Domain (NMS_CloneRef242.Ref L D) validate child242 _ trivial)
 intro env validated events hvalidate
 have same : (⟨.ret (.ok validated),events⟩ : Obs _) =
   validate ⟨a.program_id,a.accounts,a.data,a.current_slot⟩ env := hvalidate
 have law := child242 ⟨a.program_id,a.accounts,a.data,a.current_slot⟩ env trivial
 rw [←same] at law
 have scope := NMS_Clone242Facts.successful L D scan _ env validated events law
 exact (NMS_Clone241Validate.fold L V verify child064 a domain validated scope) env

#print axioms fold
end NMS_Clone241Fold
