import NNG_DecodeProjection345
import NNG_PreludeAssociation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_PreludeProjection345
open RSL NNG_Phases345 NNG_Obs345 NNG_Pure345
open NNG_LogicalProjection345 (V C)

theorem source (s : Parent) (next : Decoded V C → Obs (Except ProgramError Bytes))
 (later : ∀ d,next (NNG_LogicalProjection345.decoded d)=next d) :
 NNG_PreludeAssociation345.canonical (NNG_LogicalProjection345.parent s) next=
 NNG_PreludeAssociation345.canonical s next := by
 unfold NNG_PreludeAssociation345.canonical stepDistinct
 dsimp only [NNG_LogicalProjection345.parent]
 rw [show requireDistinct [NNG_ProjectAccounts345.account s.proofAccount,
    NNG_ProjectAccounts345.account s.publicAccount,NNG_ProjectAccounts345.account s.checkpointAccount]=
   requireDistinct [s.proofAccount,s.publicAccount,s.checkpointAccount] from
    NNG_ProjectAccounts345.distinct [s.proofAccount,s.publicAccount,s.checkpointAccount]]
 apply congrArg (tryObs (silent (requireDistinct [s.proofAccount,s.publicAccount,s.checkpointAccount])))
 funext _
 unfold stepReadonlyProof
 dsimp only
 rw [NNG_ProjectAccounts345.buffer]
 apply congrArg (tryObs (silent (readonlyBuffer s.proofAccount)))
 funext _
 unfold stepReadonlyPublic
 dsimp only
 rw [NNG_ProjectAccounts345.buffer]
 apply congrArg (tryObs (silent (readonlyBuffer s.publicAccount)))
 funext _
 unfold stepCheckpoint
 dsimp only
 change tryObs (checkpointObservation true (NNG_ProjectAccounts345.account s.checkpointAccount) s.original.program_id true) _=
  tryObs (checkpointObservation true s.checkpointAccount s.original.program_id true) _
 rw [NNG_ProjectAccounts345.checkpoint]
 apply congrArg (tryObs (checkpointObservation true s.checkpointAccount s.original.program_id true))
 funext _
 unfold stepCheckpointData
 dsimp only
 change tryObs (cloned true (s.checkpointAccount.bytes.map NNG_Cut345.cut)) _=
  tryObs (cloned true s.checkpointAccount.bytes) _
 rw [NNG_ProjectionBind345.cloned_map]
 apply congrArg (tryObs (cloned true s.checkpointAccount.bytes))
 funext ck
 unfold stepZero
 dsimp only
 rw [NNG_Cut345.zero]
 apply congrArg (tryObs (silent (requireZero ck)))
 funext _
 unfold stepPublicData
 dsimp only
 change tryObs (cloned true (s.publicAccount.bytes.map NNG_Cut345.cut)) _=
  tryObs (cloned true s.publicAccount.bytes) _
 rw [NNG_ProjectionBind345.cloned_map]
 apply congrArg (tryObs (cloned true s.publicAccount.bytes))
 funext pub
 exact NNG_DecodeProjection345.source ⟨⟨s,ck⟩,pub⟩ next later
#print axioms source
end AspisR1.NNG_PreludeProjection345
