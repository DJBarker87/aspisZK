"""Read-only deployed wrapper source association; no compiler/native execution."""
from pathlib import Path
import hashlib,json,subprocess,sys
E=Path('evidence/pv-evh10-20261102')
sha=lambda b:hashlib.sha256(b).hexdigest()
pin=next(v for v in json.load(open(E/'native-sources.json'))['library'] if '/zeroize-1.9.0/' in v['path'])
snapshot=E/'zero-wrapper-source.json'
if '--check' not in sys.argv:
 raw=subprocess.check_output(['ssh','dombarker@100.108.41.90','cat '+pin['path']])
 assert sha(raw)==pin['sha256']
 snapshot.write_text(json.dumps(dict(path=pin['path'],sha256=pin['sha256'],text=raw.decode()),indent=2)+'\n')
s=json.load(open(snapshot));assert s['path']==pin['path'] and sha(s['text'].encode())==pin['sha256']==s['sha256']
def body(anchor):
 text=s['text'];start=text.index(anchor);a=text.index('{',start);depth=1;b=a+1
 while depth:
  depth+=(text[b]=='{')-(text[b]=='}');b+=1
 return text[a:b]
associations=[
 ('pub fn new(value: Z) -> Self','{ Self(value) }','PV_EVH_ZeroWrappers.new','wrap owned value without changing it'),
 ('fn deref(&self) -> &Z','{ &self.0 }','PV_EVH_ZeroWrappers.deref','borrow original inner value'),
 ('fn deref_mut(&mut self) -> &mut Z','{ &mut self.0 }','PV_EVH_ZeroWrappers.derefMut','borrow inner value and retain identity backward restoration'),
 ('fn as_ref(&self) -> &T','{ self.0.as_ref() }','PV_EVH_ZeroWrappers.asRef','delegate to supplied AsRef dictionary'),
 ('fn as_mut(&mut self) -> &mut T','{ self.0.as_mut() }','PV_EVH_ZeroWrappers.asMut','delegate to supplied AsMut dictionary, preserving its backward function'),
]
steps=[]
for anchor,expected,law,meaning in associations:
 b=body(anchor);assert ''.join(b.split())==''.join(expected.split()),anchor
 steps.append(dict(anchor=anchor,body=b,body_sha256=sha(b.encode()),law=law,meaning=meaning))
# This impl and Drop have the same delegation; both complete bodies are checked.
for anchor in ['impl<Z> Zeroize for Zeroizing<Z>','impl<Z> Drop for Zeroizing<Z>']:
 b=body(anchor);assert 'self.0.zeroize();' in b and b.count('self.0.zeroize();')==1
 expected='{ fn '+('drop' if 'Drop' in anchor else 'zeroize')+'(&mut self) { self.0.zeroize(); } }'
 assert ''.join(b.split())==''.join(expected.split())
 steps.append(dict(anchor=anchor,body=b,body_sha256=sha(b.encode()),law='PV_EVH_ZeroWrappers.zeroize' if 'Zeroize for' in anchor else 'PV_EVH_StackZero.drop',meaning='delegate to inner Zeroize, with deployed memory/history effects retained separately'))
result=dict(evidence_class='structural source association (own-1)',source=dict(path=s['path'],sha256=s['sha256']),steps=steps,
 retained=['V370','supplied AsMut/AsRef dictionary fidelity','physical stack admission and source buffer association','full entry native coverage','L3 joint observation'],trust_fields_added=[],rows_removed=[])
out=E/'zero-wrapper-binding.json'
if '--check' in sys.argv: assert json.load(open(out))==result
else: out.write_text(json.dumps(result,indent=2)+'\n')
print('PASS seven deployed Zeroizing wrapper bodies; entry obligations retained')
