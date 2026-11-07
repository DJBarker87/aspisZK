"""Factor only the authenticated suffix, matching exact source indentation.
The rfl factor theorems must compile; no parsed/source endpoint is assumed.
"""
from pathlib import Path
import hashlib,json
E=Path(__file__).resolve().parent
p=E/'NMS_242Prefix.lean';old=p.read_text();foot='\nend NMS_242Prefix\n'
original={
 'owned':(E/'NMS_Owned242.lean').read_text(),
 'raw':(E.parent/'tx2-entry2-20261110/NLM_Validate242.lean').read_text()}
parts=[]
for kind,source in original.items():
 begin=source.index('def G (ops');end=source.index('\ndef finish',begin) if kind=='owned' else source.index('\nend NLM_Validate242',begin)
 text=source[begin:end].replace('def G (ops','def '+kind+' (ops',1)
 lines=text.splitlines();start=next(i for i,l in enumerate(lines) if l.startswith(' '*16+'let r4 ←'))
 finish=next(i for i in range(start+1,len(lines)) if lines[i].startswith(' '*14+'| core.ops.control_flow.ControlFlow.Break residual'))
 call=('NMS_242Auth.owned ops child before inputOwners val verifier_program accounts pool_program val1 val2' if kind=='owned' else 'NMS_242Auth.raw ops val verifier_program accounts pool_program val1 val2')
 lines[start:finish]=[' '*16+call]
 text='\n'.join(lines)+'\n';text=text.replace('  Run Ambient (core.result.Result','  NMS_Owned242.Run Ambient (core.result.Result').replace('  Run (core.result.Result','  NJU_Log.Run RawEvent (core.result.Result')
 parts.append(text)
header=old[:old.index('def owned')];p.write_text(header+'\n'.join(parts)+foot)
(E/'NMS_FACTOR_INPUTS.json').write_text(json.dumps({k:hashlib.sha256(v.encode()).hexdigest() for k,v in original.items()},indent=1)+'\n')
