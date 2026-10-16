#!/usr/bin/env python3
"""Pin both account helpers and the admitted flags-only buffer helper/wrapper."""
from pathlib import Path
import argparse,hashlib,json,subprocess
P=Path(__file__).resolve().parent
ap=argparse.ArgumentParser()
ap.add_argument('--check',action='store_true')
ap.add_argument('--revision',help='exact production source revision; --check defaults to recorded pin')
args=ap.parse_args()
revision=args.revision or (json.loads((P/'source-pins.json').read_text())['source_revision'] if args.check else 'HEAD')
REV=subprocess.check_output(['git','rev-parse',revision],cwd=P,text=True).strip()
SOURCES=['programs/r1-cost-probe/src/r1_pool_adapter.rs',
         'programs/aspis-verifier/src/v7_pair_forest_dispatch.rs']
def sha(data):return hashlib.sha256(data).hexdigest()
cuts=[];helpers=[];wrappers=[];tests=[]
for source in SOURCES:
    raw=subprocess.check_output(['git','show',REV+':'+source],cwd=P)
    lines=raw.decode().splitlines(keepends=True);spans={}
    names=['readonly_meta_ok','require_readonly_account']
    if source==SOURCES[0]:names+=['readonly_buffer_meta_ok','require_readonly_buffer']
    for name in names:
        start=next(i for i,l in enumerate(lines) if l.startswith('fn '+name+'('))
        end=next(i for i in range(start,len(lines)) if lines[i]=='}\n')
        body=''.join(lines[start:end+1]);spans[name]={'span':[start+1,end+1],'sha256':sha(body.encode()),'declaration':body}
    helpers.append(spans['readonly_meta_ok']['declaration'])
    wrappers.append(spans['require_readonly_account']['declaration'])
    test_path=str(Path(source).parent/'readonly_meta_tests.rs')
    test_bytes=subprocess.check_output(['git','show',REV+':'+test_path],cwd=P)
    tests.append(test_bytes)
    cuts.append({'source':source,'source_sha256':sha(raw),'declarations':spans,
                 'native_test_source':test_path,'native_test_sha256':sha(test_bytes)})
buffer=cuts[0]['declarations']['readonly_buffer_meta_ok']['declaration']
buffer_test='programs/r1-cost-probe/src/readonly_buffer_tests.rs'
buffer_test_bytes=subprocess.check_output(['git','show',REV+':'+buffer_test],cwd=P)
cuts[0].update(buffer_native_test_source=buffer_test,
               buffer_native_test_sha256=sha(buffer_test_bytes))
assert helpers[0]==helpers[1]
assert wrappers[0]==wrappers[1]
assert tests[0]==tests[1]
text='''#![allow(dead_code)]
// Exact production helper; real SDK Pubkey/ProgramError, no AccountInfo model.
pub mod readonly_meta {
use solana_pubkey::Pubkey;
use solana_program_error::{ProgramError, ProgramResult};

'''+helpers[0]+'\n'+buffer+'}\n'
pins={'source_revision':REV,'sources':cuts,'identical_helpers':True,
      'identical_wrappers':True,'identical_native_tests':True,
      'scope':'Actual pure account and buffer helpers. Wrapper text is pinned but not extracted; one R16 metadata projection is conditional, not SDK semantics or custody.',
      'kit_files':{n:sha((P/n).read_bytes()) for n in ['Cargo.toml','extract.py']}}
pins['kit_files']['lib.rs']=sha(text.encode())
if args.check:
    assert (P/'lib.rs').read_text()==text
    assert json.loads((P/'source-pins.json').read_text())==pins
    print('PASS: account helpers/wrappers/tests identical; admitted buffer helper/wrapper/tests pinned')
else:
    (P/'lib.rs').write_text(text);(P/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
