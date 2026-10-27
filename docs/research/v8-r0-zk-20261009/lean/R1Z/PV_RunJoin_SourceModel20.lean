import R1Z.PV_RunJoin_SourceColumns20
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SourceModel20
open Aeneas Aeneas.Std Result R0Z.WriterRefine
open BuilderForestAdmissionPort.pool_v1.pair_forest_copy_builder
open PV_Src_Forest_PrimitiveArguments PV_RunJoin_ReferenceFixtureResults
variable {K : Type} [Field K] [CharP K 2147483647]

theorem source (w : RW) (p : RP) (pt : Parts) (hp : parts w p = ok pt)
    (actual : CopyBanks) (ha : CopyRecords.banks ⟨w,p⟩ = ok (some actual))
    (pub : R0P.Public K) (hP : PubCorr (wordPublic p) pub)
    (hW : WitnessOk (wordWitness w)) :
    ∀ c r, liftU (K := K) (PV_Src_Forest_Columns.read actual.merged c r) =
      R0Z.BuilderModel.buildModel pub (toModel (wordWitness w)) c r := by
  obtain ⟨_,_,_,_,_,hmodel⟩ := builder_witness_merged (wordWitness w) (wordPublic p) pub hP hW
  intro c r
  rw [(PV_RunJoin_SourceColumns20.source w p pt hp actual ha).2]
  exact hmodel c r
#print axioms source

theorem transfer (pub : R0P.Public K) (hP : PubCorr (wordPublic transferPublic) pub) :
    ∀ c r, liftU (K := K) (PV_Src_Forest_Columns.read PV_RunJoin_SourceBanks19.transferBank.merged c r) =
      R0Z.BuilderModel.buildModel pub (toModel (wordWitness transferWitness)) c r := by
  obtain ⟨pt,hp⟩ := PV_RunJoin_PartsTotal19.transfer
  exact source _ _ pt hp _ PV_RunJoin_SourceBanks19.transfer pub hP transfer_checked
#print axioms transfer

theorem withdrawal (pub : R0P.Public K) (hP : PubCorr (wordPublic withdrawalPublic) pub) :
    ∀ c r, liftU (K := K) (PV_Src_Forest_Columns.read PV_RunJoin_SourceBanks19.withdrawalBank.merged c r) =
      R0Z.BuilderModel.buildModel pub (toModel (wordWitness withdrawalWitness)) c r := by
  obtain ⟨pt,hp⟩ := PV_RunJoin_PartsTotal19.withdrawal
  exact source _ _ pt hp _ PV_RunJoin_SourceBanks19.withdrawal pub hP withdrawal_checked
#print axioms withdrawal
end R1Z.PV_RunJoin_SourceModel20
