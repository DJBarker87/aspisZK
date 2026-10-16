#!/usr/bin/env python3
"""Pin both identical production helpers and their real AccountInfo wrappers."""
from pathlib import Path
import argparse,hashlib,json,subprocess
P=Path(__file__).resolve().parent
REV='20672afeffd5757f8f8eb024a71a1ce86001c7e2'
SOURCES=['programs/r1-cost-probe/src/r1_pool_adapter.rs',
         'programs/aspis-verifier/src/v7_pair_forest_dispatch.rs']
def sha(data):return hashlib.sha256(data).hexdigest()
cuts=[];helpers=[];wrappers=[];tests=[]
for source in SOURCES:
    raw=subprocess.check_output(['git','show',REV+':'+source],cwd=P)
    lines=raw.decode().splitlines(keepends=True);spans={}
    for name in ['readonly_meta_ok','require_readonly_account']:
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
assert helpers[0]==helpers[1]
assert wrappers[0]==wrappers[1]
assert tests[0]==tests[1]
text='''#![allow(dead_code)]
// Exact production helper; real SDK Pubkey/ProgramError, no AccountInfo model.
pub mod readonly_meta {
use solana_pubkey::Pubkey;
use solana_program_error::{ProgramError, ProgramResult};

'''+helpers[0]+'}\n'
pins={'source_revision':REV,'sources':cuts,'identical_helpers':True,
      'identical_wrappers':True,'identical_native_tests':True,
      'scope':'Actual pure helper only. Wrapper text is pinned but not extracted; R16 metadata projection is conditional, not SDK semantics or custody.',
      'kit_files':{n:sha((P/n).read_bytes()) for n in ['Cargo.toml','extract.py']}}
pins['kit_files']['lib.rs']=sha(text.encode())
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
if args.check:
    assert (P/'lib.rs').read_text()==text
    assert json.loads((P/'source-pins.json').read_text())==pins
    print('PASS: both exact helpers, SDK-field wrappers, and native test files byte-identical')
else:
    (P/'lib.rs').write_text(text);(P/'source-pins.json').write_text(json.dumps(pins,indent=2)+'\n')
