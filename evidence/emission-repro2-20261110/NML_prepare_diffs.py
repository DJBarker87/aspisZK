"""Retain exact scalar declaration segments for the two inverse-blob comparisons."""
from pathlib import Path
import json,hashlib,subprocess,re
E=Path(__file__).resolve().parent;O=E.parent/'emission-repro-20261110';sha=lambda b:hashlib.sha256(b).hexdigest()
bs=[b for b in json.load(open(O/'NMH_PROVENANCE.json'))['blobs'] if b['blob'].startswith(('44062509','d9cad559'))]
raw=(O/bs[0]['reproduced_path']).read_text()
def segment(s,name):
 m=re.search(r'(?m)^def '+re.escape(name)+r'\s',s);end=s.find('\n/--',m.start());return s[m.start():end].rstrip()+'\n'
inputs=[];text='import Aeneas\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\n'
for i,b in enumerate(bs):
 old=subprocess.check_output(['git','show','HEAD:'+b['committed_paths'][0]]).decode();seg=segment(old,'field.M31.add')
 inputs.append(dict(blob=b['blob'],path=b['committed_paths'][0],definition='field.M31.add',segment_sha256=sha(seg.encode())))
 text+='namespace NML_Old'+str(i)+'\nabbrev field.M31 := Std.U32\ndef field.P : Std.U32 := 2147483647#u32\n'+seg+'end NML_Old'+str(i)+'\n\n'
seg=segment(raw,'field.M31.add');inputs.append(dict(path=str(O/bs[0]['reproduced_path']),definition='field.M31.add',segment_sha256=sha(seg.encode()),emitted_blob_sha256=sha(raw.encode())))
text+='namespace NML_Emitted\nabbrev field.M31 := Std.U32\ndef field.P : Std.U32 := 2147483647#u32\n'+seg+'end NML_Emitted\n\nnamespace NML_Diffs\n'
for i in range(2):
 text+=f'''theorem old{i}_overflow : NML_Old{i}.field.M31.add (4294967295#u32) (1#u32) = fail .integerOverflow := by rfl
#print axioms old{i}_overflow
'''
text+='''theorem emitted_wrap : NML_Emitted.field.M31.add (4294967295#u32) (1#u32) = ok (0#u32) := by rfl
#print axioms emitted_wrap
'''
for i in range(2):
 text+=f'''theorem body_difference{i} : NML_Old{i}.field.M31.add ≠ NML_Emitted.field.M31.add := by
 intro h
 have point := congrFun (congrFun h (4294967295#u32)) (1#u32)
 rw [old{i}_overflow, emitted_wrap] at point
 cases point
#print axioms body_difference{i}
'''
text+='end NML_Diffs\n'
(E/'NML_DiffArithmetic.lean').write_text(text)
(E/'NML_DIFF_BODY_MAP.json').write_text(json.dumps(dict(inputs=inputs,transformation='Exact add bodies; only enclosing namespaces and definitionally identical U32 aliases / numeric P are supplied. These are paired body checks, not full-module reproduction.',domain='Full emitted scalar U32 domain. Overflow witness is outside canonical M31; no claim that canonical callers encounter it.'),indent=2)+'\n')
base=json.load(open(E.parent/'sound-int2-20261025/SInt2-001.json'));H='/home/dombarker/project-offloads/codex-cx-emission-repro2-20261110'
cfg=dict(attempt='NML_L001',kind='lean',module='NML_DiffArithmetic',sources=['NML_DiffArithmetic.lean','NML_DIFF_BODY_MAP.json'],upload=['NML_DiffArithmetic.lean','NML_DIFF_BODY_MAP.json'],command=base['command'][:-3]+['-o','NML_objects/NML_DiffArithmetic.olean','NML_DiffArithmetic.lean'],collect=[],timeout=180,env=base['env'],deps_fingerprint={},expected_time='Tiny exact scalar-body semantic comparison; fixed 32-bit addition, no field multiplication or recurrence',source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
# Coherent SInt2 library objects are pinned by the runner before launch.
(E/'NML_L001.json').write_text(json.dumps(cfg,indent=2)+'\n')
print(json.dumps(dict(module='NML_DiffArithmetic',blobs=len(bs),theorems=5)))
