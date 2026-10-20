"""Add binary instantiations of existing symbolic proofs; never edit inputs."""
from pathlib import Path
import re,json
P=Path(__file__).resolve().parents[2]; L=P/'lean'
names=['MerkleNodeLookupExt','MerkleNodeRecordUnique','MerkleLeafLookupExt','MerkleLeafRecordUnique','MerkleLogExt','RawByteCutTable','RawByteTableWords','RawByteLaterTableWords','RawBoundedCollision','LiteralLegacyDecoderCompletion','RawLiteralDecoderCompletion','RawFullPublicSelection','RawLiteralDecoderRestore','RawCutLiteralSamplerOrder','RawCutLiteralNextFrame','RawCutLiteralRowZeroOrder','RawCutLiteralReseedOrder','RawCutLiteralQueryOrder','RawCutLiteralQueryAdjacent','RawCutLiteralAllFrames']
mp={n:'RWire'+n for n in names}
base=['Merkle32Path','Merkle32Leaf','MerkleTable','MerkleLeafRecovery','MerkleRecordedLog','MerkleNodeCodec','MerkleLeafCodec','RawByteCutRecovery','RawByteCutStability','RawByteCollisionTargets']
mp.update({n:'Bin'+n for n in base})
# R1-prefixed imports are aliases for these modules in the cached tree.
for n in list(mp): mp['R1'+n]=mp[n]
for n in names:
 s=(L/(n+'.lean')).read_text()
 s=re.sub(r'\b('+'|'.join(sorted(mp,key=len,reverse=True))+r')\b',lambda m:mp[m[0]],s)
 s=s.replace('Fin 8','Fin 2').replace('Fin 11','Fin 5')
 s=s.replace('MerkleIndexGeometry.slots 6','BinMultiproof.slots 18')
 s=s.replace('pred 10','pred 4').replace('hgood.2.2 10','hgood.2.2 4').replace('pred 8','pred 2').replace('pred 9','pred 3').replace('hout 8','hout 2')
 if n=='RawByteTableWords':
  s=s.replace('import CanonicalCutEnrichedTranscript','import BinCanonicalCutWords\nimport RawByteTableWordsBin')
  s=s.replace('open BinRawByteCutRecovery BinRawByteCutStability CanonicalCutEnrichedTranscript','open BinRawByteCutRecovery BinRawByteCutStability CanonicalCutEnrichedTranscript (Words wordsFromMaps)\nopen BinCanonicalCutWords')
 # keep arity-independent old trace plumbing (read/lookup/current-or-before).
 if n=='RawBoundedCollision':
  s=s.replace('import RawBoundedTrace','import RawBoundedTrace\nimport RawBoundedCollision')
  start=s.index('theorem read_trace'); end=s.index('theorem no_duplex_collision')
  s=s[:start]+'open RawBoundedCollision (read_trace lookup_before current_or_before)\n\n'+s[end:]
  for x in ['read_trace','lookup_before','current_or_before']: s=s.replace('#print axioms '+x+'\n','')
 if n=='RawFullPublicSelection':
  s=s.replace('import FullPublicTotalCase','import FullPublicTotalCase\nimport RawFullPublicSelection')
  start=s.index('def select :='); end=s.index('theorem bounded_at_first_cell')
  s=s[:start]+'abbrev select := RawFullPublicSelection.select\n\n'+s[end:]
  s=s.replace('unfold select','unfold select RawFullPublicSelection.select')
 # every newly declared theorem, including private helpers, audited.
 decls=re.findall(r'^(?:private )?(?:@\[[^\n]+\] )?theorem (\w+)',s,re.M)
 insert='\n'.join('#print axioms '+d for d in decls if '#print axioms '+d+'\n' not in s)+'\n'
 pos=s.rfind('end AspisR1.')
 s=s[:pos]+insert+s[pos:]
 (L/(mp[n]+'.lean')).write_text(s)
(Path(__file__).parent/'derived-modules.json').write_text(json.dumps(mp,indent=2)+'\n')
