"""Generate site codecs from explicit typed occurrences; no extraction or proof evaluation."""
from pathlib import Path
import json
E=Path(__file__).resolve().parent
spec=json.loads((E/'NKE_CODEC_SPEC.json').read_text())
for lane,rows in spec.items():
 module='NKE_'+lane+'Codec'
 context='VTop_Stages NJU_CommonObserved' if lane=='Common' else 'NID_ResumeEmission NJU_ResumeObserved'
 imports='NJU_CommonObserved' if lane=='Common' else 'NJU_ResumeObserved'
 lines=['import NKE_Free','import '+imports,'set_option autoImplicit false','noncomputable section','namespace '+module,
        'open Aeneas Aeneas.Std Result AspisR1 '+context,'open NKE_Free','']
 for row in rows:
  name=row['name'];args=row['args'];signature=' '.join('('+n+' : '+t+')' for n,t in args);names=' '.join(n for n,_ in args)
  pattern=' '.join('x'+str(i) for i in range(len(args)))
  predicate=' ∧ '.join('x'+str(i)+'='+n for i,(n,_) in enumerate(args))
  lines += [f'def {name} {signature} : Codec Event ({row["reply"]}) := by',' classical',
    f' refine {{encode := .{name} {names}',
    '         decode := fun event=>match event with',
    f'          | .{name} {pattern} reply=>if {predicate} then some reply else none',
    '          | _=>none','         roundtrip := ?_}', ' intro reply',' simp','']
 if lane=='Resume':
  lines+=['def raw (n : Usize) (reader : verifier.Reader) : Codec Event (Array U8 n × verifier.Reader) := by',
   ' classical',' refine {encode := .raw n reader',
   '         decode := fun event=>match event with',
   '          | .raw n1 reader1 reply=>if h : n1=n then',
   '              if reader1=reader then some (h ▸ reply) else none',
   '             else none','          | _=>none','         roundtrip := ?_}',
   ' intro reply',' simp','']
 for row in rows:lines+=['#print axioms '+row['name']]
 if lane=='Resume':lines+=['#print axioms raw']
 lines+=['end '+module]
 (E/(module+'.lean')).write_text('\n'.join(lines)+'\n')
