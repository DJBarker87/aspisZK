"""Forward opening calls; no accepted wrapper or query decoder is assumed."""
from pathlib import Path
import sys
P=Path(__file__).resolve().parent;R=P.parents[1];files={}
for row in range(27,33):
 count=8 if row==31 else 1;mod=f'JGg_Opening{row}';ns='AspisR1.'+mod
 imps=[f'JGe_Q{row}Absorb']+[f'JGe_Q{row}{kind}{i}' for i in range(count) for kind in ['Read','Ratchet']]+['JGe_OpeningInit','F3J_QueryPairs']
 if row in [27,29,30,31]:imps += [f'JGg_Input{row}']
 else:imps += [f'JGe_Q{row-1}Ratchet'+('2' if row==32 else '0')]
 out=[f'import {m}' for m in imps]+['set_option autoImplicit false',f'namespace {ns}','open Aeneas Aeneas.Std Result AspisR1PublicPreparation','open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge']
 if row in [27,29,30,31]:out += [f'def before : State := JGg_Input{row}.before',f'def payload : Slice U8 := JGg_Input{row}.payload']
 else:out += [f'def before : State := JFp_SHADigest.output JGe_Q{row-1}Ratchet'+('2' if row==32 else '0')+'.result', 'def payload : Slice U8 := '+('⟨List.replicate 32 0#u8,by simp;scalar_tac⟩' if row==28 else '⟨[],by simp⟩')]
 length={27:928,28:32,29:224,30:256,31:2048,32:0}[row]
 out += [f'def absorbed : State := JFp_SHADigest.output JGe_Q{row}Absorb.result']
 for i in range(count):out += [f'def block{i} : State := JFp_SHADigest.output JGe_Q{row}Read{i}.result',f'def next{i} : State := JFp_SHADigest.output JGe_Q{row}Ratchet{i}.result']
 out += [f'theorem absorbInput : (flatten (CallerStep.openingAbsorbParts (encodeState before) {160+row}#u8 {length}#u32 payload)).map Fin.val=JGe_Q{row}Absorb.message := '+(f'JGg_Input{row}.native' if row in [27,29,30,31] else 'by rfl'),'#print axioms absorbInput',f'theorem absorbHash : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (CallerStep.openingAbsorbParts (encodeState before) {160+row}#u8 {length}#u32 payload)=encodeState absorbed := by','  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest',f'  rw [absorbInput,JGe_Q{row}Absorb.checked]','  rfl','#print axioms absorbHash']
 for i in range(count):
  prev='absorbed' if i==0 else f'next{i-1}'
  for kind,tag in [('read',1),('advance',2)]:
   label='Read' if kind=='read' else 'Ratchet';dest=f'block{i}' if kind=='read' else f'next{i}'
   out += [f'theorem {kind}Input{i} : (flatten (TranscriptStep.readParts (encodeState {prev}) {tag}#u8)).map Fin.val=JGe_Q{row}{label}{i}.message := by rfl',f'#print axioms {kind}Input{i}',f'theorem {kind}Hash{i} : MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState {prev}) {tag}#u8)=encodeState {dest} := by','  unfold MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest',f'  rw [{kind}Input{i},JGe_Q{row}{label}{i}.checked]','  rfl',f'#print axioms {kind}Hash{i}']
 out += [f'theorem length : payload.length={length} := '+(f'JGe_Payload{row}.length' if row in [27,29,30,31] else 'by simp only [payload,Slice.length,List.length_replicate,List.length_nil]'),'#print axioms length','attribute [local irreducible] payload before absorbed','theorem absorb {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :','    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)',f'    transcript.Transcript.absorb D0 (⟨encodeState before,hash⟩ : transcript.Transcript Hash) {row}#u8 payload=ok (⟨encodeState absorbed,hash⟩ : transcript.Transcript Hash) := by','  dsimp only',f'  have len : Slice.len payload={length}#usize := by','    apply UScalar.eq_of_val_eq','    exact length',f'  have cast : UScalar.cast .U32 (Slice.len payload)={length}#u32 := by rw [len];scalar_tac',f'  rw [CallerStep.opening_absorb_eq _ _ {row}#u8 {160+row}#u8 payload {length}#u32 (by rfl) cast]','  change (do let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest',f'             (CallerStep.openingAbsorbParts (encodeState before) {160+row}#u8 {length}#u32 payload))','             ok (⟨s,hash⟩ : transcript.Transcript Hash))=_','  rw [absorbHash,bind_tc_ok]','#print axioms absorb']
 if row!=31:
  out += ['theorem source {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :','    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)',f'    transcript.Transcript.block D0 (⟨encodeState before,hash⟩ : transcript.Transcript Hash) {row}#u8 payload=ok (encodeState block0,(⟨encodeState next0,hash⟩ : transcript.Transcript Hash)) := by','  dsimp only','  rw [transcript.Transcript.block,absorb]','  simp only [bind_tc_ok,lift]','  change (do let b ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 1#u8))','             let s ← ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest (TranscriptStep.readParts (encodeState absorbed) 2#u8))','             ok (b,(⟨s,hash⟩ : transcript.Transcript Hash)))=_','  rw [readHash0,bind_tc_ok,advanceHash0,bind_tc_ok]','#print axioms source']
 else:
  out += ['theorem pairs {Hash : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 Hash) (hash : Hash) :','    let D0 := AspisR1CurrentCaller.InstalledPreparation.retainedDigest (F3V_OracleDictionary.current JFp_SHADigest.digest D)','    ∃ calls,F3J_QueryPairs.Pairs D0 hash 8 (encodeState absorbed) calls := by','  dsimp only','  refine ⟨_,?_⟩']
  for i in range(8):
   out += ['  apply F3J_QueryPairs.Pairs.cons',f'  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState block{i})',f'    rw [readHash{i}]',f'  · change ok (MultiproofConePhysicalTransport.rawOracle JFp_SHADigest.digest _)=ok (encodeState next{i})',f'    rw [advanceHash{i}]']
  out += ['  exact .nil _','#print axioms pairs']
 out += [f'end {ns}'];text='\n'.join(out)+'\n'
 if row in [28,32]:
  needle=f'=JGe_Q{row}Absorb.message := by rfl'
  proof=f'''=JGe_Q{row}Absorb.message := by
  have le : (core.num.U32.to_le_bytes {length}#u32).val.map (fun x=>x.val)={list(length.to_bytes(4,'little'))} := by
    simp [core.num.U32.to_le_bytes,BitVec.toLEBytes] <;> (repeat' constructor) <;> scalar_tac
  simp only [flatten,CallerStep.openingAbsorbParts,Array.to_slice,Array.make,List.flatMap_cons,List.flatMap_nil,List.map_append,List.append_nil,List.map_map,Function.comp_def,decodeByte,List.map_cons,List.map_nil]
  rw [le]
  rfl'''
  text=text.replace(needle,proof)
 if row==31:
  calls=[]
  for i in range(8):
   prev='absorbed' if i==0 else f'next{i-1}'
   for tag,dest in [(1,f'block{i}'),(2,f'next{i}')]:calls.append(f'(TranscriptStep.readParts (encodeState {prev}) {tag}#u8,encodeState {dest})')
  text=text.replace('  refine ⟨_,?_⟩','  refine ⟨['+','.join(calls)+'],?_⟩')
 files[R/'lean'/(mod+'.lean')]=text
for p,s in files.items():
 if '--check' in sys.argv:
  checked_path=p if p.exists() else p
  assert checked_path.read_text()==s,checked_path
 else:p.write_text(s)
print('checked' if '--check' in sys.argv else 'generated',len(files),'opening call modules')
