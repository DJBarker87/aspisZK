"""Exact retained row25 limbs, bounded codec windows, and array decoding."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1]
row=json.loads((R/'evidence/joint-fixture11-20261026/JFm_WINDOWS.json').read_text())[25]
chunks=[row['frame'][5+i:5+i+32] for i in range(0,3712,32)];assert len(chunks)==116
vals=[[int.from_bytes(bytes(c[j:j+4]),'little') for j in range(0,16,4)] for c in chunks];assert all(x<2147483647 for v in vals for x in v)
us=lambda xs:'['+','.join(f'{x}#u8' for x in xs)+']'
q=lambda v:'⟨⟨'+','.join(f'{x}#u32' for x in v[:2])+'⟩,⟨'+','.join(f'{x}#u32' for x in v[2:])+'⟩⟩'
files={};base='''import JFu_Q25InputBase
import JFu_FlatWindow
import JFr_EncodedCell
import JFu_DecodeAt
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
'''
base+='def chunks : List (List U8) := ['+','.join(f'p{i:02}' for i in range(116))+']\n'
base+='theorem lengths : ∀ c ∈ chunks,c.length=32 := by\n  intro c hc\n  simp only [chunks,List.mem_cons,List.not_mem_nil,or_false] at hc\n  rcases hc with '+'|'.join(f'h{i}' for i in range(116))+'\n'
base+=''.join('  · subst c;rfl\n' for _ in range(116))+'#print axioms lengths\n'
for i,v in enumerate(vals):base+=f'def q{i:03} : aspis_core.field.QM31 := {q(v)}\n'
for i in range(4):base+=f'def a{i} : Array aspis_core.field.QM31 29#usize := ⟨['+','.join(f'q{j:03}' for j in range(29*i,29*(i+1)))+'],by rfl⟩\n'
base+='def claims : ClaimsUnrolledFinish.MainClaims := ⟨[a0,a1,a2],by rfl⟩\n'
base+='end AspisR1.JFu_ClaimsData\n';files[R/'lean/JFu_ClaimsData.lean']=base
for group in range(4):
 text='''import JFu_ClaimsData
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result RetainedFieldByteCodec
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open JFu_Q25Source.Input
'''
 for i in range(29*group,29*(group+1)):
  text+=f'def cell{i:03} : Array U8 16#usize := ⟨{us(chunks[i][:16])},by rfl⟩\n'
  text+=f'def limbs{i:03} : QM31Limbs := !['+','.join(f'⟨{x},by change {x}<2147483647;omega⟩' for x in vals[i])+']\n'
  text+=f'''theorem window{i:03} : ((JFu_Q25Source.record.framed.val.drop 5).drop (32*{i})).take 16=cell{i:03}.val := by
  rw [show JFu_Q25Source.record.framed.val=JFw_NativeRow25.record.val from rfl,frameBytes]
  change (chunks.flatten.drop (32*{i})).take 16=cell{i:03}.val
  rw [JFu_FlatWindow.source chunks lengths {i} (by change {i}<116;omega)]
  rfl
#print axioms window{i:03}
theorem encoded{i:03} : CandidateParserByteOrder.arrayBytes16 cell{i:03}=encodeQM31LE limbs{i:03} := by
  funext i;fin_cases i <;> rfl
#print axioms encoded{i:03}
theorem parser{i:03} : AspisR1DecodeKFullV10.aspis_core.field.QM31.from_le_bytes (Array.to_slice cell{i:03})=
    ok (some {q(vals[i])}) := JFr_EncodedCell.parser cell{i:03} limbs{i:03} encoded{i:03}
#print axioms parser{i:03}
'''
 text+='end AspisR1.JFu_ClaimsData\n';files[R/f'lean/JFu_ClaimsBytes{group}.lean']=text
for group in range(4):
 offset=29*group
 text=f"""import JFu_ClaimsBytes{group}
import JFv_MainDecode
set_option autoImplicit false
namespace AspisR1.JFu_ClaimsData
open Aeneas Aeneas.Std Result AspisR1PublicPreparation AspisS1ExtractedRoundChildren

theorem decode{group} : decodeMain 29#usize JFu_Q25Source.record {offset}#usize=ok (.Ok a{group}) := by
  have canonical := PSem_FieldCanonical.source_payload 25#u8 JFw_NativeRow25.record JFw_NativeRow25.payload
    (by change 14≤25;omega) JFw_NativeRow25.accepted
  have shape : JFu_Q25Source.record.framed.length=3717 := by
    simp only [JFu_Q25Source.record,JFw_NativeRow25.record,JFw_Frames.frame,Slice.length,List.length_cons]
    have size : JFw_NativeRow25.payload.val.length=3712 := JFw_NativeRow25.payload_length
    omega
  obtain ⟨out,call⟩ := JFv_MainDecode.success 29#usize JFu_Q25Source.record {offset}#usize
    (by change 14≤25;omega) (by rw [shape];change 5+32*({offset}+29)≤3717;omega)
    (by rw [shape];omega) canonical
  have cells : ∀ j : Fin 29,out.val[j.val]'(by rw [out.property];exact j.isLt)=
      a{group}.val[j.val]'(by rw [a{group}.property];exact j.isLt) := by
    intro j
    fin_cases j
"""
 for j in range(29):
  i=offset+j
  text+=f'    · exact JFu_DecodeAt.source JFu_Q25Source.record out {offset}#usize (by change {offset}≤116;omega) call ⟨{j},by change {j}<29;omega⟩ cell{i:03} _ window{i:03} parser{i:03}\n'
 text+=f"""  have same : out=a{group} := by
    apply Subtype.ext
    apply List.ext_getElem
    · rw [out.property,a{group}.property]
    · intro i hi hj
      exact cells ⟨i,by rw [out.property] at hi;exact hi⟩
  exact same ▸ call
#print axioms decode{group}
end AspisR1.JFu_ClaimsData
"""
 files[R/f'lean/JFu_ClaimsDecode{group}.lean']=text
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('claims preflight:',len(files),'modules;',len(vals),'bounded 16-byte decoder cells; no whole-buffer reduction')
