"""Reify the exact retained caller body, preserving every std operation and call argument."""
from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;P=E.parent/'tx2-native8-20261108';rows=[]
p=P/'NJU_CommonObserved.lean';source=p.read_text();body=source[source.index('def run '):source.index('/-- Forward erasure')]
body=body.replace('NJU_Log.Run','NKE_Free.Program')
body=re.sub(r'NJU_Log.record\s+\(\.(\w+)',lambda m:'NKE_Free.record (NKE_CommonCodec.'+m[1],body)
text='\n'.join(['import NKE_CommonCodec','set_option autoImplicit false','noncomputable section','namespace NKE_CommonProgram','open Aeneas Aeneas.Std Result VTop_Stages AspisR1 NJU_CommonObserved','',body,'end NKE_CommonProgram',''])
(E/'NKE_CommonProgram.lean').write_text(text);rows.append({'source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'output':'NKE_CommonProgram.lean','transformation':'Run→Program; record ctor→site codec only; body otherwise literal'})
p=P/'NJU_ResumeObserved.lean';source=p.read_text();base=source[source.index('def recordRaw '):source.index('def finishTailG ')]
base=base.replace('NJU_Log.Run','NKE_Free.Program')
base=re.sub(r'NJU_Log.record\s+\(\.(\w+)',lambda m:'NKE_Free.record (NKE_ResumeCodec.'+m[1],base)
header=['import NKE_ResumeCodec','set_option autoImplicit false','noncomputable section','namespace NKE_ResumeProgram','open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission NJU_ResumeObserved','']
(E/'NKE_ResumeProgramBase.lean').write_text('\n'.join(header+[base,'end NKE_ResumeProgram','']))
prev='NKE_ResumeProgramBase'
for i,name in enumerate(['finishTailG','queryEndG','queryMidG','queryBlockG','resumeBodyG','run'],1):
 start=source.index('def '+name+' ');end=source.find('\ndef ',start+4);body=source[start:end if end>=0 else len(source)]
 body=body.replace('NJU_Log.Run','NKE_Free.Program')
 # References resolve to the own outlined G definitions, not to NJU's writer.
 module='NKE_ResumeProgram'+str(i)
 (E/(module+'.lean')).write_text('\n'.join(['import '+prev]+header[1:]+[body,'end NKE_ResumeProgram','']))
 rows.append({'source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'declaration':name,'output':module+'.lean','transformation':'Run→Program only; helper references resolve to NKE_ResumeProgram'})
 prev=module
(E/'NKE_PROGRAM_SOURCE_PINS.json').write_text(json.dumps(rows,indent=2)+'\n')
