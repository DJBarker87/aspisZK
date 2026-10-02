#!/usr/bin/env python3
"""Verify the saved R398 translation receipt and first diagnostic; no rerun."""
from pathlib import Path
import hashlib,json,re
HERE=Path(__file__).resolve().parent
LAUNCH=HERE/'launch-history/13617a70553e-20261002T165818Z'
OUT=HERE/'output/13617a70553e-20261002T165818Z'
llbc=Path('.r21-scratch/r396-private-batch-unmonomorphized-plan/R396PrivateBatchUnmonomorphized.llbc')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
source='399020435e94aaa7135c06d68445e9b936bd22fe6d1e1d197ee708d448d584ae'
binary='f12977c5acd368d268d3af9562110ab29be60d7b4055dde937d0049f85409db5'
assert sha(llbc)==source
receipt=json.loads((LAUNCH/'launch-result.json').read_text());cmd=json.loads((OUT/'translate-command.json').read_text());result=json.loads((OUT/'result.json').read_text())
assert receipt['input_sha256']==cmd['source_sha256']==result['source_sha256']==source
assert receipt['binary_sha256']==cmd['binary_sha256']==result['binary_sha256']==binary
assert receipt['launcher_exit_status']==result['translator_exit_status']==2 and receipt['scp_exit_status']==0
assert cmd['namespace']=='AspisR398GenericBatch' and cmd['sequential'] and cmd['abort_on_error'] and cmd['split_files'] and cmd['emit_json']
assert cmd['scope_caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}
assert not (OUT/'generated').exists()
log=(OUT/'translate.log').read_text()
first='Internal error, please file an issue'
where='SymbolicToPureTypes.ml, line 1047'
assert first in log and where in log and 'core/src/iter/traits/iterator.rs' in log
metrics={'wall_time':re.search(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([^\n]+)',log).group(1),'max_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',log).group(1)),'swaps':int(re.search(r'Swaps: (\d+)',log).group(1)),'time_exit_status':int(re.search(r'Exit status: (\d+)',log).group(1))}
assert metrics=={'wall_time':'0:00.23','max_rss_kib':71280,'swaps':0,'time_exit_status':2},metrics
assert receipt['caps']=={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128}
report={'result':'verified saved R398 failed translation receipt; no rerun','input_llbc_sha256':sha(llbc),'binary_sha256':binary,'launch_revision':receipt['launch_revision'],'source_revision':receipt['source_revision'],'remote_payload_sha256':receipt['remote_payload_sha256'],'launcher_exit_status':receipt['launcher_exit_status'],'scp_exit_status':receipt['scp_exit_status'],'translator_exit_status':result['translator_exit_status'],'translation_output_generated':False,'metrics':metrics,'first_diagnostic':'Aeneas internal error on iterator.rs:2486:4–2490:35 in symbolic/SymbolicToPureTypes.ml:1047; stack includes sanity_check_opt_span during translate_fun_sigs.','resource_caps':receipt['caps'],'reservation_gate':'passed: 53,597,404 kB MemAvailable, all prior aspis slice cgroups empty, no heavy compiler/translator processes, active slice caps 0','print_axioms':'N/A, no Lean target or compilation','scope':'Full unchanged R396 LLBC translation inventory attempt only; no LLBC rewrite, template filling, Lean compile, or source/security claim.'}
(HERE/'saved-evidence-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
