from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
manifest=json.loads((P/'JGe_WINDOWS_MANIFEST.json').read_text());files={}
for row,off,n,width in [(27,7031,464,16),(29,7527,224,32),(30,7751,256,32),(31,8007,2048,32)]:
 cells=n//width;ns=f'AspisR1.JGe_Payload{row}'
 out=[f'import {m}' for m in manifest['order'] if m.startswith(f'JGe_Window{row}_')]+['import JGe_WindowAssembly','import JGe_ValuesAssembly','import JFw_Y1','set_option autoImplicit false',f'namespace {ns}','open Aeneas Aeneas.Std Result',f'open JGe_Window{row}','attribute [local irreducible] JFx_NativeBytes.proofBytes']
 out += ['def rawChunks : List (List U8) := ['+','.join(f'c{i:02}' for i in range(cells))+']',f'theorem retained : (JFw_Frames.window {off} {n}).val=rawChunks.flatten := by',f'  have h := JGe_WindowAssembly.source {width} {cells} {off}','  simpa only [JGe_WindowAssembly.chunks,Nat.reduceAdd,rawChunks,'+','.join(f'selected{i:02}' for i in range(cells))+'] using h','#print axioms retained']
 if row==27:
  out += ['theorem lengths : ∀ c∈rawChunks,c.length=16 := by','  intro c hc','  simp only [rawChunks,List.mem_cons,List.not_mem_nil,or_false] at hc','  rcases hc with '+' | '.join(f'h{i}' for i in range(cells))]+['  · subst c;rfl' for _ in range(cells)]+['#print axioms lengths']
  out += ['def sourceChunks : List (List U8) := rawChunks.map (fun c => c ++ List.replicate 16 0#u8)','def value : Slice U8 := JFw_Frames.expandedPayload 29 7031 (by decide) (by decide)','theorem bytes : value.val=sourceChunks.flatten := by','  change (JFw_Blocks.blocks 29 (JFw_Frames.window 7031 464).val).flatten=_','  rw [retained]','  exact congrArg List.flatten (JGe_ValuesAssembly.source rawChunks lengths)','#print axioms bytes','theorem source : AspisS1ValuesOwnedInstallation.expandValues JFw_Y1.stored JFw_Y1.initial=ok (.Ok (),value) := by','  obtain ⟨out,call,size,hbytes⟩ := JFw_Y1.inhabited','  have expected := JFw_Frames.expanded_bytes 29 7031 (by decide) (by decide)','  have same : out=value := Subtype.ext (MultiproofConeByteEquality.bytes_injective (hbytes.trans expected.symm))','  exact same ▸ call','#print axioms source','theorem length : value.length=928 := JFw_Frames.expanded_length 29 7031 (by decide) (by decide)','#print axioms length']
 else:
  out += [f'def value : Slice U8 := JFw_Frames.window {off} {n}',f'theorem length : value.length={n} := JFw_Frames.window_length {off} {n} (by decide)','#print axioms length']
 out += [f'end {ns}'];files[R/'lean'/f'JGe_Payload{row}.lean']='\n'.join(out)+'\n'
for p,s in files.items():
 if '--check' in sys.argv:assert p.read_text()==s,p
 else:p.write_text(s)
print('checked' if '--check' in sys.argv else 'generated',len(files),'source payload modules')
