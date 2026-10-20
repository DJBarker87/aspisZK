from pathlib import Path
import json,re
E=Path(__file__).parent; L=E.parents[1]/'lean'
mp=json.loads((E/'derived-modules.json').read_text())
more=['RawCutLaterTableLiteralWords','LiteralTableChoiceWords','RawLiteralRecordedDecoder','RawLiteralCompiledDecoder','RawCompiledTranscript','RawCompiledDecoderCompletion','RawFullPublicRun','RawAdaptiveCompiledCompletion']
mp.update({n:'RWire'+n for n in more}); mp['RawCutConstructedWords']='RWireConstructedWords'
for n in more:
 s=(L/(n+'.lean')).read_text()
 s=s.replace('RawCutWordsFromView.buildWords','BinCompiledRunWordStability.wordsFromRun')
 s=s.replace('LiteralTableWordChoice.choose','LiteralTableWordChoiceBin.choose')
 s=s.replace('CanonicalCutEnrichedTranscript.full','BinCanonicalCutWords.full')
 s=re.sub(r'\b('+'|'.join(sorted(mp,key=len,reverse=True))+r')\b',lambda m:mp[m[0]],s)
 s=s.replace('Fin 11','Fin 5').replace('Fin 8','Fin 2').replace('MerkleIndexGeometry.slots 6','BinMultiproof.slots 18')
 s=s.replace('pred 8','pred 2').replace('pred 9','pred 3').replace('0x71 480 8','0x71 480 2').replace('0xf1 128 8','0xf1 128 2').replace('0x72 128 9','0x72 128 3')
 s=s.replace('open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript','open LiteralDecoderEnrichment CanonicalCutEnrichedTranscript (Words wordsFromMaps enrichPrefix enrichMessage)\nopen BinCanonicalCutWords')
 if n=='RawCutLaterTableLiteralWords': s=s.replace('open AspisR1.CanonicalCutEnrichedTranscript','open AspisR1.CanonicalCutEnrichedTranscript (Words wordsFromMaps)\nopen BinCanonicalCutWords')
 s='import BinCompiledRunWordStability\nimport LiteralTableWordChoiceBin\n'+s
 decls=re.findall(r'^(?:private )?theorem (\w+)',s,re.M)
 pos=s.rfind('end AspisR1.')
 s=s[:pos]+'\n'.join('#print axioms '+d for d in decls if '#print axioms '+d+'\n' not in s)+'\n'+s[pos:]
 (L/('RWire'+n+'.lean')).write_text(s)
# Root-reader bridge, reusing the unchanged frame grammar.
s=(L/'RawCutConstructedWords.lean').read_text(); s=s[:s.index('/-- With the existing strict parsers')]
s=s.replace('import RawCutCommitmentFrames','import RawCutConstructedWords\nimport BinCompiledRunWordStability')
s=s.replace('namespace AspisR1.RawCutConstructedWords','namespace AspisR1.RWireConstructedWords')
# Retain the original root lemmas, then convert their conclusions by parser equality.
s=s.replace('RawByteCollisionTargets.pred 8','BinRawByteCollisionTargets.pred 2').replace('RawByteCollisionTargets.pred 9','BinRawByteCollisionTargets.pred 3')
s=s.replace('(j : Fin 11)','(j : Fin 5)').replace('(RawByteCollisionTargets.pred j)','(BinRawByteCollisionTargets.pred j)').replace('RawByteCollisionTargets.pred j','BinRawByteCollisionTargets.pred j')
s=s.replace('exact RawCutCommitmentFrames.initial_root _ root w','simpa only [BinRawByteCollisionTargets.pred_tail, RawByteCollisionTargets.pred_tail] using RawCutCommitmentFrames.initial_root _ root w')
s=s.replace('exact RawCutCommitmentFrames.c2_root _ m w root hdecode','simpa only [BinRawByteCollisionTargets.pred_tail, RawByteCollisionTargets.pred_tail] using RawCutCommitmentFrames.c2_root _ m w root hdecode')
s=s.replace('exact RawCutCommitmentFrames.second_root _ m w payload hdecode','simpa only [BinRawByteCollisionTargets.pred_middle, RawByteCollisionTargets.pred_middle] using RawCutCommitmentFrames.second_root _ m w payload hdecode')
# append bin full-word theorem, actual-cuts proof written separately below
orig=(L/'RawCutConstructedWords.lean').read_text(); t=orig[orig.index('theorem buildWords_eq_full_from_messages'):orig.index('#print axioms initial_root')]
t=t.replace('RawCutWordsFromView.buildWords','BinCompiledRunWordStability.wordsFromRun').replace('RawByteCollisionTargets.pred Q','BinRawByteCollisionTargets.pred Q').replace('(fullC1Map','(BinCanonicalCutWords.fullC1Map').replace('(fullC2Map','(BinCanonicalCutWords.fullC2Map').replace('(fullFoldedMap','(BinCanonicalCutWords.fullFoldedMap')
t=t[:t.index(' := by')]+''' := by
  dsimp only
  let v := eval H (experiment P (verifier decoder d))
  have h0' := initial_root decoder H v.2.1.1 v.2.1.2 c1root c1 h0
  have h2' := c2_root decoder H v.2.1.1 v.2.1.2 c2msg c2 c2root h2 hc2
  have h30' := second_root decoder H v.2.1.1 v.2.1.2 secondmsg final second h30 hsecond
  unfold BinCompiledRunWordStability.wordsFromRun
  rw [RawCutWordsFromView.frameFromView_eq decoder d P H 0 (by decide),
    RawCutWordsFromView.frameFromView_eq decoder d P H 2 (by decide),
    RawCutWordsFromView.frameFromView_eq decoder d P H 30 (by decide)]
  have h0old := RawCutConstructedWords.initial_root decoder H _ _ c1root c1 h0
  have h2old := RawCutConstructedWords.c2_root decoder H _ _ c2msg c2 c2root h2 hc2
  have h30old := RawCutConstructedWords.second_root decoder H _ _ secondmsg final second h30 hsecond
  simp only [RawCutWordsFromView.rootFrom, h0old, h2old, h30old, Option.getD_some]
  exact BinCanonicalCutWords.wordsFromRawCuts_eq_full iv H v.1 Q
    (FS.eval_consistent H _) hQ hout _ _ _ _ _ _ 2 2 3
    (RawCutWordsFromView.frame_read decoder d P H 0 (by decide))
    (RawCutWordsFromView.frame_read decoder d P H 2 (by decide))
    (RawCutWordsFromView.frame_read decoder d P H 30 (by decide)) h0' h2' h30'

'''
s+=t+'\n'.join('#print axioms '+n for n in ['pred_getD_of_bind','initial_root','c2_root','second_root','buildWords_eq_full_from_messages'])+'\nend AspisR1.RWireConstructedWords\nend\n'
(L/'RWireConstructedWords.lean').write_text(s)
