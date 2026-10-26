"""Read-only receipt/source audit. Does not compile, launch or monitor jobs."""
from pathlib import Path
import collections, hashlib, json, re, subprocess, tomllib
ROOT=Path(__file__).resolve().parents[2]
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
load=lambda p:json.loads(p.read_text())
errors=[]
def check(test,message):
    if not test: errors.append(message)
receipts=[(p,load(p)) for p in sorted(E.glob('PoolS2_*/receipt.json'))]
lean=[(p,r) for p,r in receipts if re.fullmatch('PoolS2_L[0-9]{3}',r['attempt'])]
kani=[(p,r) for p,r in receipts if re.fullmatch('PoolS2_K[0-9]{3}',r['attempt'])]
check([r['attempt'] for p,r in lean]==[f'PoolS2_L{i:03}' for i in range(1,101)],'Lean actual attempt inventory')
check([r['attempt'] for p,r in kani]==[f'PoolS2_K{i:03}' for i in range(1,26)],'Kani actual attempt inventory')
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
for p,r in receipts:
    check(r['limits']==limits,f'{p}: scope limits')
    check(str(r['swaps'])=='0',f'{p}: swaps')
    for src,digest in r['source_hashes'].items():
        target=p.parent/'sources'/src
        check(target.is_file() and sha(target)==digest,f'{p}: snapshot {src}')
    if r['kind']=='lean':
        check('-M7000' in r['command'],f'{p}: Lean memory cap')
    if r['kind']=='kani':
        check(r['env'].get('CARGO_PROFILE_DEV_OPT_LEVEL')=='3',f'{p}: optimized Kani')
    if r['kind']=='charon':
        check('--release' in r['command'],f'{p}: optimized Charon')
    if r['exit_status']==0 and r['kind']=='lean':
        for item in r['print_axioms']:
            for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]',item,re.S):
                names={x.strip() for x in group.split(',') if x.strip()}
                check(names <= {'propext','Classical.choice','Quot.sound'},f'{p}: axioms {names}')
module_matches={}
host=load(E/'PoolS2_HOST_FINAL.json')
for p in sorted((ROOT/'lean').glob('PoolS2_*.lean')):
    digest=sha(p)
    passed=[r['attempt'] for q,r in lean if r['exit_status']==0 and r['source_hashes'].get(p.name)==digest]
    check(bool(passed),f'{p}: no passing receipt for current bytes')
    check(host['modules'][p.name]['source_sha256']==digest,f'{p}: host source mismatch')
    check(not re.search(r'^\s*(axiom\s|unsafe\s|.*:=\s*(sorry|admit)\b)',p.read_text(),re.M),f'{p}: forbidden proof placeholder')
    module_matches[p.name]={'sha256':digest,'passing_attempts':passed,'host_olean_sha256':host['modules'][p.name]['olean_sha256']}
inputs=load(E/'PoolS2_INPUTS.json')['inputs']
for x in inputs:
    check(sha(ROOT/x['path'])==x['sha256'],'local shipped input '+x['path'])
check(host['matched']==len(inputs) and not host['mismatches'],'host input equality')
check('PoolS2-' not in host['own_active_scopes'],'own active scope remains')
changed=subprocess.check_output(['git','diff','--name-only','60c70c8d0ec110f8ec2967a1ffa1ec0f2dfb00dd'],cwd=ROOT,text=True).splitlines()
untracked=subprocess.check_output(['git','ls-files','--others','--exclude-standard'],cwd=ROOT,text=True).splitlines()
for name in changed+untracked:
    check(name.startswith('evidence/pool-write5-20261026/') or re.fullmatch(r'lean/PoolS2_.*\.lean',name) is not None,'outside prefix '+name)
locks={}
for crate in ['PoolS2_ref','PoolS2_prefix','PoolS2_snapshot','PoolS2_planner']:
    lock=E/crate/'PoolS2_resolved.lock';m=tomllib.loads(lock.read_text())
    locks[crate]={'sha256':sha(lock),'selected_sdk_versions':{name:[x['version'] for x in m['package'] if x['name']==name] for name in ['solana-account-info','solana-pubkey','solana-sdk-ids']}}
audit=load(E/'PoolS2_L100/receipt.json')
check(audit['exit_status']==1,'preserved final audit must remain failed')
log=(E/'PoolS2_L100/stdout.log').read_text()
check(len(re.findall('error\\(lean.unknownIdentifier\\)',log))==3,'audit error inventory')
check(len(audit['print_axioms'])==133,'audit successful entries')
for item in audit['print_axioms']:
    for group in re.findall(r'depends on axioms:\s*\[([^]]*)\]',item,re.S):
        check({x.strip() for x in group.split(',') if x.strip()} <= {'propext','Classical.choice','Quot.sound'},'audit nonstandard axiom')
def stats(rows):
    return {'attempts':len(rows),'exit_status_counts':dict(collections.Counter(str(r['exit_status']) for p,r in rows)),
        'sum_measured_wall_seconds':sum(r['wall_seconds'] for p,r in rows),
        'max_time_peak_rss_kib':max(int(r['peak_rss_kib']) for p,r in rows if str(r['peak_rss_kib']).isdigit()),
        'max_cgroup_memory_peak_bytes':max(int(r.get('cgroup_memory_peak_bytes',0)) for p,r in rows),
        'swaps':sorted({str(r['swaps']) for p,r in rows})}
result={'status':'PASS' if not errors else 'FAIL','errors':errors,
    'revision_before_final_receipt_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
    'dirty_receipt_files_expected':True,'input_count':len(inputs),'current_modules':module_matches,
    'lean':stats(lean),'kani':stats(kani),'resolved_proof_only_locks':locks,
    'final_audit':{'exit':1,'standard_axiom_entries':133,'missing_names':['PoolS2_Unique.PoolS2_Unique.key_equal','PoolS2_Unique.PoolS2_Unique.right_unique','PoolS2_Unique.PoolS2_Unique.unique_keys'],'original_three_roots_passed':'PoolS2_L001','excluded_from_delivered_lean_tree':True},
    'warning':'Kani outer-timeout /usr/bin/time peakRSS can undercount descendants. cgroup peaks recorded separately. No native P1/refinement, release, source-to-SBF or deployment claim.'}
(E/'PoolS2_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['current_modules','resolved_proof_only_locks']},indent=2))
raise SystemExit(bool(errors))
