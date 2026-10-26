"""Generate per-window native decoder certificates, never whole-buffer reduction."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1];rows=json.loads((P/'JFr_coefficients.json').read_text());outputs={}
for row in rows:
 r=row['round'];off=row['offset'];native=f'JFw_NativeRow{15+r:02}';m=f'JFr_Decode{r:02}';b=f'JFr_Bytes{r:02}';roundm=f'JFr_Round{r:02}'
 s=f'''import {b}
import {roundm}
import JFr_BlockWindow
import JFv_MainDecode
import {native}
set_option autoImplicit false
noncomputable section
namespace AspisR1.{m}
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation AspisS1ExtractedRoundChildren
open {b}

def record : r1_wire.ValidatedRecord := ⟨{15+r}#u8,{native}.record⟩
'''
 for i in range(28):
  s+=f'''theorem window{i:02} : ((record.framed.val.drop 5).drop (32*{i})).take 16=cell{i:02}.val := by
  change (((JFw_Blocks.blocks 28 (JFw_Frames.window {off} 448).val).flatten).drop (32*{i})).take 16=cell{i:02}.val
  have same : (JFw_Frames.window {off} 448).val=raw := selected
  rw [same,JFr_BlockWindow.source 28 raw (by rfl) {i} (by omega)]
  rfl
#print axioms window{i:02}
'''
 s+=f'''theorem source : decodeMain 28#usize record 0#usize=ok (.Ok {roundm}.polynomial) := by
  have canonical := PSem_FieldCanonical.source_payload {15+r}#u8 {native}.record {native}.payload (by omega) {native}.accepted
  have shape : record.framed.length=901 := by
    change 5+{native}.payload.val.length=901
    have size : {native}.payload.val.length=896 := {native}.payload_length
    omega
  obtain ⟨out,call⟩ := JFv_MainDecode.success 28#usize record 0#usize (by change 14≤{15+r};omega)
    (by rw [shape];change 5+32*(0+28)≤901;omega) (by rw [shape];omega) canonical
  have cells : ∀ j : Fin 28,out.val[j.val]'(by rw [out.property];exact j.isLt)=
      {roundm}.polynomial.val[j.val]'(by rw [{roundm}.polynomial.property];exact j.isLt) := by
    intro j
    fin_cases j
'''
 for i in range(28):
  s+=f'    · exact JFr_DecodeCell.source record out call ⟨{i},by omega⟩ cell{i:02} _ window{i:02} parser{i:02}\n'
 s+=f'''  have same : out={roundm}.polynomial := by
    apply Subtype.ext
    apply List.ext_getElem
    · rw [out.property,{roundm}.polynomial.property]
    · intro i hi hj
      exact cells ⟨i,by rw [out.property] at hi;exact hi⟩
  exact same ▸ call

#print axioms source
end AspisR1.{m}
end
'''
 outputs[m]=s
for m,s in outputs.items():
 f=R/'lean'/(m+'.lean')
 if '--check' in sys.argv:assert f.read_text()==s,m
 else:f.write_text(s)
print(json.dumps(dict(modules=len(outputs),checked='--check' in sys.argv,exceptional='No huge recurrence cell: each 16-byte parser window uses a symbolic block-stride lemma and a named codec inverse.')))
