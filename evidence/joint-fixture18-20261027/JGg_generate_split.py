from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1]
src=(R/'docs/research/100bit-spend-path-20261013/lean/bridge-opening-queries-1b98-20261017/ExtractedOpeningQueriesModel.lean').read_text()
start=src.index('  let r ← B.decode blocks15 blocks16')
end=src.index('\n#print',start)
tail=src[start:end].replace('blocks15 blocks16','blocks advances').replace('aspis_coreDigest32Inst','D')
# Original trailing function has no additional declarations before the audits.
head='''import JGg_QueryTrace
set_option autoImplicit false
namespace AspisR1.JGg_QuerySplit
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisV8R19.SqueezeOracleBridge
abbrev Bytes32 := Array U8 32#usize
abbrev Blocks := Array Bytes32 8#usize
'''
out=head+'''def finish (B : QueriesModel.Boundaries) {Hash : Type} (D : aspis_core.Digest32 Hash) (self1 : transcript.Transcript Hash)
    (blocks advances : Blocks) : Result (core.result.Result (Array U32 22#usize) verifier.Error × transcript.Transcript Hash) := do
'''+tail+'\n'
out+='''def step {Hash A : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (i : Usize) (state : Bytes32) (blocks advances : Blocks)
    (k : Blocks → Blocks → Bytes32 → Result A) : Result A := do
  let read ← D.digest hash (TranscriptStep.readParts state 1#u8)
  let blocks1 ← Array.update blocks i read
  let next ← D.digest hash (TranscriptStep.readParts state 2#u8)
  let advances1 ← Array.update advances i next
  let state1 ← Array.index_usize advances1 i
  k blocks1 advances1 state1

def later {Hash A : Type} (D : aspis_core.Digest32 Hash) (hash : Hash)
    (blocks advances : Blocks) (state : Bytes32) (k : Blocks → Blocks → Result A) : Result A :=
'''
for i in range(1,8):
 out+='  '*i+f'step D hash {i}#usize state blocks advances fun blocks advances state =>\n'
out+='  '*8+'k blocks advances\n'
out+='''def initial {Hash A : Type} (D : aspis_core.Digest32 Hash) (self : transcript.Transcript Hash)
    (row : U8) (payload : Slice U8) (k : transcript.Transcript Hash → Blocks → Blocks → Result A) : Result A := do
  let self1 ← transcript.Transcript.absorb D self row payload
  let zero := Array.repeat 32#usize 0#u8
  let blocks := Array.repeat 8#usize zero
  let read ← D.digest self1.hash (TranscriptStep.readParts self1.state 1#u8)
  let (_,back) ← Array.index_mut_usize blocks 0#usize
  let next ← D.digest self1.hash (TranscriptStep.readParts self1.state 2#u8)
  let advances := back next
  let state ← Array.index_usize advances 0#usize
  later D self1.hash (back read) advances state (k self1)

end AspisR1.JGg_QuerySplit
'''
p=R/'lean/JGg_QuerySplit.lean'
if '--check' in sys.argv:assert p.read_text()==out
else:p.write_text(out)
print('checked' if '--check' in sys.argv else 'generated','query CPS split')
