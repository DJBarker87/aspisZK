from pathlib import Path
import subprocess,json,hashlib
from NEM_install import install
from NEM_artifacts import ref,theorem,native_support
from NEM_validator_checks import CASES
E=Path(__file__).resolve().parent
for case,spec in CASES.items():
 f=spec['function'];source=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+f.split('::')[0]],text=True);a=source.index('fn '+f.split('::')[1]+'(');z=source.index('\n}',a)+2;body=source[a:z]
 ts=[theorem('NEM_FrontierValidatorInstance',case+'_step'),theorem('NEM_FrontierValidatorInstance',case+'_result_and_frame')]
 q=dict(case=case,function=f,method='native scalar prefix plus arbitrary frontier step; accepted NBH induction',all_typed_inputs=True,all_raw_frontiers=True,empty_external_modifies=True,prefix=spec['prefix'],step=spec['step'],invariant='0<=level<=20; original frontier; exact external frame; next scanner argument=frontier[level]',ordered_children='root first, then increasing frontier indices until first rejection',trust_classification='P6/D188 option A reclassification',native_support=native_support(spec['prefix']+spec['step']),frozen_body=body,frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),loop_source=body[body.index('    let mut level = 0;'):body.rindex('    Ok(())')],theorems=ts,induction='NBH_FrontierTrace over NBD_DigestTrace.Trace; NBH_LiveValidator.source / NBH_Validators.afterstate')
 install(f,'frontier_validator',q,ts,[ref(E/a/'receipt.json') for a in spec['prefix']+spec['step']],ts[:1],ts[1:],'Actual '+case+' validator on every typed record. Exact native scalar prefix preserves all rejection cases and the same root scanner argument. One actual while iteration at arbitrary level<=20 binds the original frontier cell, complete Result, next cursor, and local ordered call log. The composed tree scanner has a total all-raw domain and empty external modifies. Accepted NBH induction and emitted step association compose the same original frontier from level zero through first rejection or exhaustion; no whole-frontier Kani scan or new trust row. P6/D188 option A reclassification.')
