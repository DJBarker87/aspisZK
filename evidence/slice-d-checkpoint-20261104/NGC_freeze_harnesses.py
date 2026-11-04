from pathlib import Path
import json,subprocess,difflib,hashlib
E=Path(__file__).resolve().parent;F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';x=json.loads((E/'NGC_NATIVE_INPUTS.json').read_text());patch=[];inputs={}
for n,s in x.items():
 old=''if '/NGC_'in n else subprocess.check_output(['git','show',F+':'+n],text=True)
 patch.extend(difflib.unified_diff(old.splitlines(True),s.splitlines(True),fromfile='a/'+n if old else '/dev/null',tofile='b/'+n))
 inputs[n]=dict(sha256=hashlib.sha256(s.encode()).hexdigest(),frozen_sha256=hashlib.sha256(old.encode()).hexdigest()if old else None)
p=E/'NGC_HARNESSES.patch';p.write_text(''.join(patch));(E/'NGC_HARNESSES.patch.sha256').write_text(hashlib.sha256(p.read_bytes()).hexdigest()+'\n');(E/'NGC_FINAL_NATIVE_INPUT_PINS.json').write_text(json.dumps(inputs,indent=1)+'\n')
