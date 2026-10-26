"""Read-only receipt/source checks; no build, launcher, or prover invocation."""
from pathlib import Path
import hashlib,json,re,subprocess
B=Path(__file__).resolve().parent
R=B.parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def body(src,name):
 start=src.index('fn '+name);pos=src.index('{',start);depth=1;end=pos+1
 while depth:
  depth+=(src[end]=='{')-(src[end]=='}');end+=1
 return src[start:end]
checks={}
pins=json.loads((R/'evidence/pool-scope-20261026/PoolS_source-pins.json').read_text())
for p,meta in pins['files'].items():assert sha(R/p)==meta['sha256'],p
checks['unchanged_inherited_scope_inputs']=len(pins['files'])
leaf=(B/'PoolM_leaf/PoolM_lib.rs').read_text()
for file,names in [('processor.rs',['require_prepared_plan_account_v1','close_program_account_v1','plan_fresh_program_pda','require_fresh_rent_exempt_program_pda','require_unique_accounts']),('history.rs',['require_program_account']),('pair_forest.rs',['require_program_owned_zeroed'])]:
 src=(R/'programs/aspis-pool/src'/file).read_text()
 for name in names:assert body(src,name)==body(leaf,name),name
checks['literal_native_helpers']=7
for spec in json.loads((B/'PoolM_SLICES.json').read_text()):
 data=(R/spec['file']).read_bytes()[spec['start']:spec['end']]
 assert hashlib.sha256(data).hexdigest()==spec['sha256'],spec['name']
checks['initial_slices_pinned']=True
m=json.loads((B/'PoolM_CPI_META_SLICE.json').read_text());data=(R/m['file']).read_bytes()[m['start']:m['end']]
assert hashlib.sha256(data).hexdigest()==m['sha256']
checks['cpi_meta_span_pinned']=True
raw=(B/'PoolM_cancelrolestyped-generated/PoolM_CancelRolesTyped/Funs.lean').read_text()
raw=raw[raw.index('/-- Trait implementation:'):raw.index('\nend PoolM_CancelRolesTyped')]
raw=raw.replace('def require_prepared_plan_account_v1\n','def require_prepared_plan_account_v1\n  (readLength : solana_account_info.AccountInfo → Result Usize)\n')
raw=raw.replace('solana_account_info.AccountInfo.data_len account','readLength account')
raw=raw.replace('def PoolM_cancel_roles_native\n','def PoolM_cancel_roles_native\n  (readLength : solana_account_info.AccountInfo → Result Usize) (system : solana_pubkey.Pubkey)\n')
raw=raw.replace('solana_sdk_ids.system_program.id','ok system')
raw=raw.replace('← require_prepared_plan_account_v1 core_plan','← require_prepared_plan_account_v1 readLength core_plan').replace('← require_prepared_plan_account_v1 shard','← require_prepared_plan_account_v1 readLength shard')
raw=raw.replace('solana_program_error.ProgramError.InvalidAccountData','AdapterRw.solana_program_error.ProgramError.InvalidAccountData')
installed=(R/'lean/PoolM_NativeCancelSource.lean').read_text()
actual=installed[installed.index('/-- Trait implementation:'):installed.index('\nend AspisR1.PoolM_NativeCancelSource')]
assert raw==actual
checks['native_generated_body_installation_exact']=True
for name,hexval in re.findall(r'^    (\w+) = (0x[\dA-Fa-f_]+),',(R/'programs/aspis-pool/src/error.rs').read_text(),re.M):
 assert f'| .{name} => {int(hexval.replace("_",""),16)}#u32' in installed,name
checks['error_codes_from_frozen_source']=True
receipts=[]
for p in sorted(B.glob('PoolM_*/receipt.json')):
 x=json.loads(p.read_text())
 for f,h in x['source_hashes'].items():assert sha(p.parent/'sources'/f)==h,(p,f)
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'},p
 assert x['swaps']=='0',p
 if x['kind']=='lean' and x['exit_status']==0:
  assert 'sorryAx' not in '\n'.join(x['print_axioms']),p
 receipts.append(x)
checks['receipt_count']=len(receipts)
checks['budget']={'lean_reservations':24,'actual_lean_compiles':sum(x['kind']=='lean' for x in receipts),'kani_runs':sum(x['kind']=='kani' for x in receipts),'max_lean':100,'max_kani':20,'prelaunch_failure':'PoolM_LEAN012_PRELAUNCH_FAILURE.txt'}
for p in sorted((R/'lean').glob('PoolM_*.lean')):
 text=p.read_text();assert not re.search(r'\b(sorry|axiom|admit|native_decide)\b',re.sub(r'/-.*?-/', '',text,flags=re.S)),p
 if p.name!='PoolM_Source.lean':assert 'set_option maxHeartbeats' not in text and 'set_option maxRecDepth' not in text,p
 for name in re.findall(r'^theorem (\w+)',text,re.M):assert '#print axioms '+name in text,p
 candidates=[x for x in receipts if x['kind']=='lean' and x['exit_status']==0 and x['source_hashes'].get(p.name)==sha(p)]
 assert candidates,('missing exact-source green receipt',p)
checks['all_current_lean_sources_have_green_receipts_and_axioms_commands']=True
changes=subprocess.check_output(['git','diff','--name-only','2d30c4c7e4'],cwd=R,text=True).splitlines()
assert all(p.startswith('lean/PoolM_') or p.startswith('evidence/pool-nonint2-20261026/') for p in changes),changes
checks['tracked_scope_matches']=True
checks['git_head']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
checks['status']='PASS: local source-cut evidence only; exhaustive dispatch target not established'
(B/'PoolM_VALIDATION.json').write_text(json.dumps(checks,indent=2)+'\n')
(B/'PoolM_attempts.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in receipts))
print(json.dumps(checks,indent=2))
