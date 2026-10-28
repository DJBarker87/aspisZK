from pathlib import Path
import re,json,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
D=json.loads((P/'JHm_PREFLIGHT.json').read_text());rows=D['rows'][4]
bs=lambda a:'['+','.join(f'{v}#u8' for v in a)+']'
limbs=lambda a:'!['+','.join(f'⟨{x},by decide⟩' for x in a[:4])+']'
q=lambda a:'⟨⟨'+','.join(f'{x}#u32' for x in a[:2])+'⟩,⟨'+','.join(f'{x}#u32' for x in a[2:4])+'⟩⟩'
files={};name='JHm_Row26Windows'
s='''import JHm_BlockWindows\nimport JFu_DecodeAt
import JGi_FieldWindows
import JGe_Decode26
set_option autoImplicit false
namespace AspisR1.JHm_Row26Windows
open Aeneas Aeneas.Std Result
attribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes
'''
for j,row in enumerate(rows):
 b=b''.join(x.to_bytes(4,'little') for x in row[:4]);s+=f'def b{j:02} : List U8 := {bs(b)}\n'
s+='def chunks : List (List U8) := ['+','.join(f'b{j:02}++List.replicate 16 0#u8' for j in range(29))+']\n'
s+='theorem lengths : ∀ c∈chunks,c.length=32 := by\n  intro c hc\n  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hc\n  rcases hc with '+ '|'.join(f'h{j}' for j in range(29))+'\n'
for j in range(29):s+='  · subst c;rfl\n'
s+='#print axioms lengths\n'
s+='theorem selected (j : Fin 29) :\n    ((JFu_Q26Source.record.framed.val.drop 5).drop (32*j.val)).take 16=\n      ((JFw_Frames.window 6567 464).val.drop (16*j.val)).take 16 := by\n  change ((JFw_Blocks.blocks 29 (JFw_Frames.window 6567 464).val).flatten.drop (32*j.val)).take 16=_\n  have len : (JFw_Frames.window 6567 464).val.length=16*29 := by\n    rw [show (JFw_Frames.window 6567 464).val.length=464 from JFw_Frames.window_length 6567 464 (by decide)]\n  exact JHm_BlockWindows.source 29 (JFw_Frames.window 6567 464).val len j.val j.isLt\n#print axioms selected\n'
s+='end AspisR1.JHm_Row26Windows\n';files[name]=s
for start in range(0,29,10):
 end=min(29,start+10);name=f'JHm_Row26_{start:02}'
 s=f'import JHm_Row26Windows\nimport JHm_Arithmetic\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{name}\nopen Aeneas Aeneas.Std Result RetainedFieldByteCodec\nopen AspisR1PublicPreparation AspisS1ExtractedRoundChildren\nattribute [local irreducible] JFx_NativeBytes.proof JFx_NativeBytes.proofBytes\n'
 for j in range(start,end):
  row=rows[j];b=b''.join(x.to_bytes(4,'little') for x in row[:4]);s+=f'def arr{j:02} : Array U8 16#usize := ⟨JHm_Row26Windows.b{j:02},by rfl⟩\n'
  s+=f'theorem source{j:02} (out : Array aspis_core.field.QM31 29#usize)\n    (call : decodeMain 29#usize JFu_Q26Source.record 0#usize=ok (.Ok out)) :\n    out.val[{j}]'+"'(by have h:=out.property;change out.val.length=29 at h;omega)="+q(row)+''' := by
'''
  s+=f'  have selected := JHm_Row26Windows.selected (⟨{j},by decide⟩ : Fin 29)\n'
  s+=f'  have window : ((JFw_Frames.window 6567 464).val.drop (16*{j})).take 16=arr{j:02}.val := by\n'
  s+='    simp only [JFw_Frames.window,JFx_NativeBytes.proof]\n'
  s+='    rw [List.drop_take,List.drop_drop,List.take_take]\n'
  common=['List.drop_append','List.take_append','List.length_append','Nat.reduceAdd','Nat.reduceMul','Nat.reduceSub','Nat.reduceLeDiff','List.length_drop','List.drop_eq_nil_of_le','List.take_of_length_le','List.drop_zero','List.take_zero','List.nil_append','List.append_nil']
  s+='    simp only ['+','.join(['JFx_NativeBytes.proofBytes']+[f'JFx_DataProof{i:02}.length' for i in range(15)]+common)+']\n'
  s+='    simp only ['+','.join(['JFx_DataProof01.bytes']+[f'JFx_DataProof01.c{i:02}_length' for i in range(128)]+common)+']\n    rfl\n'
  s+=f'  have hs : ((JFu_Q26Source.record.framed.val.drop 5).drop (32*(0+{j}))).take 16=arr{j:02}.val := selected.trans window\n'
  s+=f'  have parser := JFr_EncodedCell.parser arr{j:02} ({limbs(row)} : QM31Limbs) (by funext i;fin_cases i <;> rfl)\n'
  s+=f'  exact JFu_DecodeAt.source JFu_Q26Source.record out 0#usize (by decide) call ⟨{j},by decide⟩ arr{j:02} _ hs parser\n#print axioms source{j:02}\n'
 s+=f'end AspisR1.{name}\nend\n';files[name]=s
for name,s in files.items():
 if '--check' in sys.argv:assert (R/'lean'/f'{name}.lean').read_text()==s,name
 else:(R/'lean'/f'{name}.lean').write_text(s)
print('Validated29 bounded scalar readback cells in4 modules')
