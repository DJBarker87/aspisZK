from pathlib import Path
import hashlib,json,re
W=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ids=json.loads((W/'source-identities.json').read_text())
for rel,h in ids['files'].items(): assert sha(W/rel)==h,(rel,h,sha(W/rel))
source=W/'source-snapshots/weights-combined-constructor-v2.rs'
assert sha(source)==ids['source_overlay']['combined_source_sha256']
text=source.read_text()
def extract(text, marker):
 s=text.index(marker); b=text.index('{',s); d=0
 for i in range(b,len(text)):
  if text[i]=='{': d+=1
  elif text[i]=='}':
   d-=1
   if d==0:return text[s:i+1]
 raise AssertionError('unclosed function')
actual_new=extract(text,'pub fn new(variant:Variant')
actual_box=extract(text,'fn box_from_parts(')
assert hashlib.sha256(actual_new.encode()).hexdigest()==ids['source_overlay']['new_method_sha256']
assert hashlib.sha256(actual_box.encode()).hexdigest()==ids['source_overlay']['box_from_parts_sha256']
assert actual_new==(W/'source-snapshots/constructor-new.rs').read_text().strip()
assert actual_box==(W/'source-snapshots/constructor-box-from-parts.rs').read_text().strip()
boxpos=text.index('fn box_from_parts(')
assert '#[inline(never)]' in text[max(0,boxpos-32):boxpos]
libtext=(W/'input/src/lib.rs').read_text()
libbox=libtext.index('fn box_from_parts(')
assert '#[inline(never)]' in libtext[max(0,libbox-40):libbox]
lib=(W/'input/src/lib.rs').read_text()
def norm(s): return re.sub(r'\s+','',s)
expected=actual_new[actual_new.index('{')+1:-1].replace('Self::box_from_parts','Weights::box_from_parts')
wrapper=extract(lib,'pub fn weights_new(')
actualbody=wrapper[wrapper.index('{')+1:-1]
assert norm(expected)==norm(actualbody),'constructor body differs beyond named wrapper normalization'
assert norm(actual_box)==norm(extract(lib,'fn box_from_parts(')),'box_from_parts body not exact'
assert 'pub fn weights_new' in lib and 'Result<Box<Weights>, Error>' in lib
cfg=json.loads((W/'attempt-config.json').read_text())
assert cfg['target_dir']=='/home/dombarker/project-offloads/s3-s9-scalar-fold-fullsysroot-v3-20261021/target'
assert cfg['aeneas_namespace']=='AspisR1S9ActualWeightsNewBoxNewV3'
assert cfg['charon_sha256']=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert cfg['aeneas_sha256']=='959659a6aafc6a6a975b4dc67ee9d779a269b988bd44b3b31a77cf023b1709e3'
print('PASS: combined 241a constructor and pack helper source bodies pinned; wrapper differs only by documented Self-to-Weights owner spelling; target/tool pins valid.')
print('OPEN: state_only_prefix fixed[7,6] normalization; Box::new allocator-failure refinement; complete 241a helper/caller extraction.')
