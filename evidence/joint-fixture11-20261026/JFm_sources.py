from pathlib import Path
import json,sys,re
from JFm_input import generate
P=Path(__file__).resolve().parent;R=P.parents[1]
rows=json.loads((P/'JFm_WINDOWS.json').read_text())
files={}
for r in rows[1:25]:
 i=r['row'];ns=f'JFm_Q{i:02}Source';prev='JFr_SeedBoundary.numeric' if i==0 else ('JFp_Query00Source.ratchet' if i==1 else f'JFm_Q{i-1:02}Source.ratchet');imports=['JFp_Query00Source' if i==1 else f'JFm_Q{i-1:02}Source',f'JFm_Q{i:02}Absorb',f'JFm_Q{i:02}Reads',f'JFw_NativeRow{i:02}','ExtractedDigest32SamplerTransport']
 if i>=15:imports=['JFm_BlockSplit']+imports
 if i>=15:imports=[x for x in imports if x not in [f'JFm_Q{i:02}Absorb',f'JFm_Q{i:02}Reads']]+[f'JFm_Q{i:02}Hashes']
 s='\n'.join('import '+x for x in imports)+'\nset_option autoImplicit false\nnamespace AspisR1.'+ns+'\nopen Aeneas Aeneas.Std Result\nopen AspisR1PublicPreparation\nopen AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge\n'
 frame='['+','.join(f'{x}#u8' for x in r['frame'])+']'
 frame_def=f'def frame : Slice U8 := ⟨{frame},by scalar_tac⟩' if i<15 else f'abbrev frame : Slice U8 := JFw_NativeRow{i:02}.record'
 s+=f'{frame_def}\ndef absorbed : State := JFp_SHADigest.output JFm_Q{i:02}Absorb.result\ndef block : State := JFp_SHADigest.output JFm_Q{i:02}Read.result\ndef ratchet : State := JFp_SHADigest.output JFm_Q{i:02}Ratchet.result\ndef record : r1_wire.ValidatedRecord := ⟨{i}#u8,JFw_NativeRow{i:02}.record⟩\n'
 s+=f'theorem realFrame : JFw_NativeRow{i:02}.record=frame := by\n  apply Subtype.ext\n  rfl\n#print axioms realFrame\n'
 if i>=15:s+=generate(i,prev,r)
 for label,part,st in [('absorb',f'TranscriptStep.absorbParts (encodeState {prev}) {160+i}#u8 frame','absorbed'),('read','TranscriptStep.readParts (encodeState absorbed) 1#u8','block'),('ratchet','TranscriptStep.readParts (encodeState absorbed) 2#u8','ratchet')]:
  mod=f'JFm_Q{i:02}'+label.capitalize()
  proof='Input.native.trans Input.regroup' if i>=15 and label=='absorb' else 'by rfl'
  s+=f'theorem {label}Input : (flatten ({part})).map Fin.val={mod}.message := {proof}\n#print axioms {label}Input\n'
  s+=f'theorem {label}Hash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest ({part})=encodeState {st} := by\n  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest\n  rw [{label}Input,{mod}.checked]\n  rfl\n#print axioms {label}Hash\n'
 s+=f'''theorem source {{Hash : Type}} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    r1_wire.SemanticTranscript.sample_block_validated D0
      (⟨encodeState {prev},hash,{i}#u8⟩ : r1_wire.SemanticTranscript Hash)
      {i}#u8 JFw_NativeRow{i:02}.record=ok (.Ok (encodeState block),
        (⟨encodeState ratchet,hash,{i+1}#u8⟩ : r1_wire.SemanticTranscript Hash)) := by
  dsimp only
  rw [realFrame,TranscriptStep.step_of_add _ _ {i}#u8 {160+i}#u8 {i+1}#u8 frame rfl (by rfl) (by rfl)]
  change (do let a ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
      (TranscriptStep.absorbParts (encodeState {prev}) {160+i}#u8 frame))
             let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 1#u8))
             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest
               (TranscriptStep.readParts a 2#u8))
             ok ((core.result.Result.Ok b : core.result.Result (Array U8 32#usize) r1_wire.Error),(⟨s,hash,{i+1}#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [absorbHash,bind_tc_ok,readHash,bind_tc_ok,ratchetHash,bind_tc_ok]
#print axioms source
'''
 rank=int.from_bytes(bytes(r['read']),'little');cs=str(r['coordinates']).replace(' ','')
 for j in range(8):
  word=int.from_bytes(bytes(r['read'][4*j:4*j+4]),'little')
  s+=f'theorem word{j:02} : AspisV8R19.SamplerWords.word block ⟨{j},by omega⟩={word} := by rfl\n#print axioms word{j:02}\n'
 s+=f'theorem rank : SourceSamplerByteRank.rank (encodeState block)={rank} := by\n  unfold SourceSamplerByteRank.rank\n  rw [state_roundtrip,←SamplerBlockRank.word_numeral_eq_rank]\n  change SamplerPass.numeral (2^32) (['+','.join(f'AspisV8R19.SamplerWords.word block ⟨{j},by omega⟩' for j in range(8))+f'].reverse)={rank}\n  rw ['+','.join(f'word{j:02}' for j in range(8))+']\n  rfl\n#print axioms rank\n'
 s+=f'theorem digits : SamplerNatModel.qm31Digits {rank}={cs} := by rfl\n#print axioms digits\n'
 s+=f'''theorem semantic {{Hash : Type}} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :
    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest
      (F3V_OracleDictionary.current JFp_SHADigest.digest D)
    ∃ q : AspisR1PublicPreparation.aspis_core.field.QM31,
    r1_wire.SemanticTranscript.semantic_validated D0
      (⟨encodeState {prev},hash,{i}#u8⟩ : r1_wire.SemanticTranscript Hash)
      record=ok (.Ok q,(⟨encodeState ratchet,hash,{i+1}#u8⟩ : r1_wire.SemanticTranscript Hash)) ∧
    ExtractedQM31SamplerCorrect.coordinates (AspisR1PublicPreparation.SamplerTransport.toOld q)={cs} := by
  obtain ⟨q,call,canon,coords⟩ := AspisR1PublicPreparation.SamplerTransport.sample_total (encodeState block)
  refine ⟨q,?_,by simpa only [rank,digits] using coords⟩
  simp only [r1_wire.SemanticTranscript.semantic_validated,record,r1_wire.ValidatedRecord.impl.row,
    r1_wire.ValidatedRecord.impl.framed,bind_tc_ok]
  rw [if_neg (by change ¬({i}:Nat)>24;omega)]
  rw [source,bind_tc_ok]
  change (do let v ← AspisR1PublicPreparation.sampler.qm31_sample (encodeState block)
             ok ((core.result.Result.Ok v : core.result.Result aspis_core.field.QM31 r1_wire.Error),
               (⟨encodeState ratchet,hash,{i+1}#u8⟩ : r1_wire.SemanticTranscript Hash)))=_
  rw [call,bind_tc_ok]
#print axioms semantic
end AspisR1.{ns}
'''
 files[R/'lean'/(ns+'.lean')]=s
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,str(f)
 else:f.write_text(s)
print(len(files))
