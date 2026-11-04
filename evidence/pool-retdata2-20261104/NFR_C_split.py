"""Observation-only splits of terminal K060; preserves original native names."""
from pathlib import Path
import json, subprocess, difflib, hashlib, sys, re
E = Path(__file__).resolve().parent
REV = '4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
mode = sys.argv[1]
assert re.fullmatch(r'(?:byte|value-[0-7])(?:-negative)?', mode), mode
negative = mode.endswith('-negative')
base_path = E / 'NFR_K060-shape.json'
base = json.loads(base_path.read_text())
source = base['source']
def replace(old, new, count=None):
 global source
 actual = source.count(old)
 assert actual == (1 if count is None else count), (old, actual)
 source = source.replace(old, new)
if mode.startswith('byte'):
 replace(' assert!(observe(r,f.family,f.row,f.word,f.index)==f.field);', '')
 replace(' assert!(runtime.calls==3&&frame.calls==1&&observe(a.value(),family,row,word,index)==observe(&reply,family,row,word,index));',
         ' assert!(runtime.calls==3&&frame.calls==1);')
 replace(' assert!(runtime.calls==3&&frame.calls==1&&observe(a.value(),family,row,word,index)==field&&a.exact_bytes()[j]==byte);',
         ' assert!(runtime.calls==3&&frame.calls==1&&a.exact_bytes()[j]==byte);')
 if negative:
  replace('out[j]==expected_byte', 'out[j]==(expected_byte^1)')
 observation = 'all runtime/decoder/settlement counts and rejection prefixes, decoder byte pointer/length/observed byte, actual getter SAME pointer at all child calls, saved and reencoded byte frames; typed value equality omitted'
else:
 family = int(mode.split('-')[1])
 replace('let family:u8=kani::any();kani::assume(family<8);', f'let family:u8={family};')
 replace('&&bytes[f.j]==f.byte', '')
 replace(' assert!(a.exact_bytes().len()==792&&a.exact_bytes()[j]==byte&&core::ptr::eq(a.exact_bytes().as_ptr(),ptr));',
         ' assert!(a.exact_bytes().len()==792&&core::ptr::eq(a.exact_bytes().as_ptr(),ptr));')
 replace('settlement.calls==3&&out.len()==792&&out[j]==expected_byte',
         'settlement.calls==3&&out.len()==792')
 replace('&&a.exact_bytes()[j]==byte', '')
 if negative:
  # Corrupt a child argument expectation while retaining the original assertion.
  replace('field,valid,next,encoded,validation_error,next_error,reply:encoded_reply',
          'field:field^1,valid,next,encoded,validation_error,next_error,reply:encoded_reply')
 observation = f'projection family {family}, all arbitrary coordinates, SAME native returned authenticated object and actual getter pointer at all child calls, runtime/decoder/settlement counts and rejection prefixes; byte equalities omitted'
patch = ''
for path in ['programs/aspis-pool/src/pair_forest_dispatch.rs', 'programs/aspis-pool/src/lib.rs']:
 frozen = subprocess.check_output(['git', 'show', REV+':'+path], text=True)
 hook = frozen+'\n#[cfg(kani)]\n#[path="NFR_CJoin.rs"]\nmod NFR_CJoin;\n' if path.endswith('pair_forest_dispatch.rs') else '#![cfg_attr(kani, feature(allocator_api))]\n'+frozen+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NFO_KMX;\n'
 patch += ''.join(difflib.unified_diff(frozen.splitlines(True), hook.splitlines(True), fromfile='a/'+path, tofile='b/'+path))
path = 'programs/aspis-pool/src/NFR_CJoin.rs'
patch += '--- /dev/null\n+++ b/'+path+'\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+line+'\n' for line in source.splitlines())
shape = dict(mode=mode, source=source, harness='pair_forest_dispatch::NFR_CJoin::association', base='NFR_K060-shape.json', base_sha256=hashlib.sha256(base_path.read_bytes()).hexdigest(), classification='Observation-only split of K060 timeout; source-exact read and settlement cuts, not enclosing Pool process', observation=observation, negative_control=negative, accepted_domain=base['accepted_domain'], retained='complete child Results, arbitrary full reply, original names, exact len=capacity792, original same authenticated object')
(E/'NFR_C_native.patch').write_text(patch)
(E/'NFR_C_CURRENT.json').write_text(json.dumps(shape, indent=1)+'\n')
