"""Generate an explicit telescope composition; no new source/model definition."""
from pathlib import Path
E=Path(__file__).resolve().parent
s=(E/'NGS_Carriers.lean').read_text();pre=s[:s.index('/-- SAME actual')].replace('import NGS_Selection\nimport NGS_CheckpointRead','import NGS_Carriers')
args=s[s.index('    (Q : Nat)'):s.index(' := by\n',s.index('theorem same_inputs_or_collision'))]
cut=args.index('    (f : FirstCut)')
first=args[:cut];rest=args[cut:]
rest=rest.replace('    (saved : alloc.vec.Vec U8)\n','')
start=rest.index('    (loaded :');end=rest.index('    (readerResult :',start);rest=rest[:start]+rest[end:]
e1='((eval H source).2).1.entry';e2='(((eval H source).2).2.2.get reached).1.entry'
extra='''    (prepared : CheckpointBytes5Writer.Prepared) (accumulator : CheckpointBytes5Writer.Accumulator)
    (domain : NGC_KNE_Caller.WriterDomain prepared accumulator)
    (hp hu hc : CheckpointBytes5Effect.Digest)
    (p : CPG_Projection.Observations Tx A) (t u : Tx)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (actions : List (CPP_BankState.Action A)) (std : S2W_TrustedStd.TrustedStd copy)
    (valid1 : Valid ENTRY1.heap) (system : S2W_ExtractionBoundary.Program)
    (data1 : Slice U8) (state1 final1 : A) (post1 : Heap (Nat → Record))
    (game : CPH_Game.DeployedPairExecution p t u ENTRY1 ENTRY2
      (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc) actions n1 n2 copy allocator id)
    (native_writer_result : first n1 copy allocator ENTRY1 id data1 state1 =
      ok (.Ok ((NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc),post1,final1)))
    (protection : CPH_Protection.Facts p t
      (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc) id)
    (ordinary : CPG_Projection.ordinary p system t ((p.layout t).handles 2).1)
    (RuntimePersistence : CPR_DataPersistence.TwoTransactionLaw
      (CPG_Projection.adjacent p) (CPG_Projection.ordinary p system)
      (CPG_Projection.before p) (CPG_Projection.tentative p)
      (CPG_Projection.success p) (CPG_Projection.loaded p))
    (L : Library W (Nat → Record)) (sdk : S2TrustedSdkBorrow L)
    (w2 : W) (related2 : L.related w2 ENTRY2.heap) (valid2 : Valid ENTRY2.heap)
'''.replace('ENTRY1',f'({e1})').replace('ENTRY2',f'({e2})')
rest=rest.replace(' saved', ' (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc)')
proof=''' := by
  obtain ⟨_,_,_,_,_,_,loaded,_,_,_⟩ := NGR_HISTORY.saved_to_loaded
    prepared accumulator domain hp hu hc p t u ENTRY1 ENTRY2 actions n1 n2 copy std
    allocator valid1 id system data1 state1 final1 post1 game native_writer_result
    protection ordinary RuntimePersistence L sdk w2 related2 valid2
  exact same_inputs_or_collision base err r hashv copy allocator a H Q bound
    reached f s finish1 proof1Index public1Index proof1Read public1Read range1 length1
    proof2Index proof2Read range2 length2 v validation encoding
    (NGR_HISTORY.checkpoint prepared accumulator domain hp hu hc) writerResult
    checkpoint2Index checkpoint2Read loaded readerResult

#print axioms saved_to_carriers
end
end AspisR1.NGS_CARRIERS
end
'''.replace('ENTRY1',f'({e1})').replace('ENTRY2',f'({e2})')
(E/'NGS_PersistedCarriers.lean').write_text(pre+'''/-- Direct NGR -> carrier composition on the response-selected entries.
The loaded-byte equality is a CONCLUSION of NGR, never an input here. Native
writer, source protection, ordinary account and SDK domains remain explicit. -/
theorem saved_to_carriers {Tx W : Type}
'''+first+extra+rest+proof)
