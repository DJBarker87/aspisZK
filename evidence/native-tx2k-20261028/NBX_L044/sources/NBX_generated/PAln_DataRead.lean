import PAln_LiteralPrefix
import PAln_RowKappa
import PAln_RowFirst
import PAln_RowLast
set_option autoImplicit false
noncomputable section
namespace AspisR1.PAln_DataRead
open AspisV8R19.DuplexFrames OraclePortCompactDraft OraclePortStoredDecisionDraftC4 RawCutTranscriptRun

theorem exists_read (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (aligned : Aligned p tr)
    (rows : semanticRows 27 0 (slice p.wire 48 6983)=some p.semantic)
    (length : p.wire.length=57607) (scan : scan p.wire)
    (typed : ∃ decoded,SemanticPrefixCodec.decodeFrom 0 (p.semantic.take 25)=some decoded)
    (ordinary : ∀ i,i<31 → ∃ value,LiteralChallengeRead.ordinaryAt (typedRows p q tr) i=some value) :
    ∃ data,LiteralMatchingData.read (typedRows p q tr)=some data := by
  let rs := typedRows p q tr
  obtain ⟨semantic,semanticRead⟩ := PAln_LiteralPrefix.semantic_read p q tr aligned rows typed ordinary
  have wordReads := PAln_AlignedRead.words_read p q tr aligned
  obtain ⟨z0,read25⟩ := ordinary 25 (by decide)
  obtain ⟨z1,read26⟩ := ordinary 26 (by decide)
  obtain ⟨gamma,read27⟩ := ordinary 27 (by decide)
  obtain ⟨kappa,read28⟩ := ordinary 28 (by decide)
  obtain ⟨alpha0,read29⟩ := ordinary 29 (by decide)
  obtain ⟨alpha1,read30⟩ := ordinary 30 (by decide)
  have len : (rs.take 25).length=25 := by
    simp only [rs,typedRows,List.length_mapIdx,List.length_take,aligned.2.2.1]
    rfl
  have view : ∃ common,LiteralOpeningView.read rs=some common := by
    simp [LiteralOpeningView.read,len,wordReads.1,wordReads.2.1,read25,read26,rs]
    split
    · rename_i absent
      rw [semanticRead] at absent
      cases absent
    · exact ⟨_,rfl⟩
  obtain ⟨common,viewRead⟩ := view
  obtain ⟨p25,d25⟩ := PAln_CircleDecode.row25 p rows
  obtain ⟨p26,d26⟩ := PAln_CircleDecode.row26 p rows
  obtain ⟨p27,d27⟩ := PAln_OpeningDecode.gamma p length scan
  obtain ⟨p28,d28⟩ := PAln_RowKappa.kappa p length scan
  obtain ⟨p29,d29⟩ := PAln_RowFirst.first p length scan
  obtain ⟨p30,d30⟩ := PAln_RowLast.second p length scan
  obtain ⟨p31,d31⟩ := PAln_RowLast.final p length scan
  have h25 := PAln_AlignedRead.readAt p q tr aligned 25 (by decide) (by decide) _ p25 d25
  have h26 := PAln_AlignedRead.readAt p q tr aligned 26 (by decide) (by decide) _ p26 d26
  have h27 := PAln_AlignedRead.readAt p q tr aligned 27 (by decide) (by decide) _ p27 d27
  have h28 := PAln_AlignedRead.readAt p q tr aligned 28 (by decide) (by decide) _ p28 d28
  have h29 := PAln_AlignedRead.readAt p q tr aligned 29 (by decide) (by decide) _ p29 d29
  have h30 := PAln_AlignedRead.readAt p q tr aligned 30 (by decide) (by decide) _ p30 d30
  have h31 := PAln_AlignedRead.readAt p q tr aligned 31 (by decide) (by decide) _ p31 d31
  have staged : LiteralOpeningStages.readSecond rs=some ⟨⟨⟨⟨p25,p26,p27⟩,p28⟩,p29⟩,p30⟩ := by
    simp only [LiteralOpeningStages.readSecond,LiteralOpeningStages.readFirst,
      LiteralOpeningStages.readKappa,LiteralOpeningStages.readGamma,rs,
      h25,h26,h27,h28,h29,h30,Bind.bind,Pure.pure]
    rfl
  unfold LiteralMatchingData.read
  rw [viewRead,staged]
  simp only [Option.bind_some,Bind.bind,Pure.pure]
  rw [h31,wordReads.2.2,read27,read28,read29,read30]
  exact ⟨_,rfl⟩

#print axioms exists_read
end AspisR1.PAln_DataRead
end
