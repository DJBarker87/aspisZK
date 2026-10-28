import ast,hashlib,json,pathlib,subprocess,time,resource,sys,re
start=time.monotonic();E=pathlib.Path(__file__).parent
for p in E.glob('*.py'):ast.parse(p.read_text(),filename=str(p))
for p in E.glob('*.json'):json.loads(p.read_text())
rows=[json.loads(l) for l in (E/'NCR_ATTEMPTS.jsonl').read_text().splitlines()]
host=[r for r in rows if r['attempt'].startswith('NCR_I') or r['attempt'].startswith('NCR_B')]
assert len(host)==5 and all(r['admission_allowed'] and r['admission_exit']==0 for r in host)
assert all(r['exit_status']==0 for r in host if r['attempt']!='NCR_I001')
b=next(r for r in host if r['attempt']=='NCR_B003');assert b['match'] and b['swaps']==0
assert b['artifact_sha256']=='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4'
assert b['source_check_before']['files']==156 and not b['source_check_after']['mismatches']
assert b['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
samples=json.loads((E/'NCR_RECEIPT_SAMPLE.json').read_text());assert len(samples)==120
scan=json.loads((E/'NCR_BODY_SCAN.json').read_text());assert scan['inventory_entries']==587
for p,sha in scan['unique_files'].items():
 data=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+p]);assert hashlib.sha256(data).hexdigest()==sha
inputs=json.loads((E/'NCR_RELEASE_INPUT_CHECK.json').read_text());assert [x['inputs'] for x in inputs]==[132,132,133] and not any(x['mismatches'] for x in inputs)
old=json.loads((E/'NCR_RELEASE_CFG.json').read_text());compared=[]
for line in (E/'NCR_I004-stdout.log').read_text().splitlines():
 j=json.loads(line)
 if 'diagnostic_file' not in j:continue
 args=j['content'];flags=[args[i+1] for i,v in enumerate(args[:-1]) if v in ['--cfg','-C','--target']]
 expected=next(x['codegen_cfg_target'] for x in old if x['mode']=='default' and x['crate']==j['diagnostic_file'].removesuffix('.json'))
 assert flags==expected,(j['diagnostic_file'],flags,expected);compared.append(j['diagnostic_file'])
assert len(compared)==4
assert '"target_absent": true' in (E/'NCR_I004-stdout.log').read_text()
key=json.loads((E/'NCR_I005-stdout.log').read_text());assert key['mode_after']=='0o600' and not key['key_deleted']
base=subprocess.check_output(['git','rev-parse','abc5202abf^']).decode().strip()
assert not subprocess.check_output(['git','diff','--name-only',base,'--','crates','programs'])
assert not [str(p) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20*1024*1024]
for n in ['NCR_FEATURE_TABLE.md','NCR_TARGET_DEPENDENT.md','NCR_SOURCE_TO_ELF.md','NCR_HANDOFF.md','NCR_ATTEMPTS.jsonl']:assert (E/n).exists()
result=dict(attempt='NCR_LOCAL_VALIDATE',kind='local_source_receipt_validation',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss if sys.platform=='darwin' else 1024*resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,source_revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),sampled_receipts=len(samples),sampled_lanes=len({s['path'].split('/')[1] for s in samples}),frozen_inventory_entries=587,default_compiler_cfg_comparisons=compared,host_scopes_used=5,Kani=0,Lean=0,print_axioms='N/A; no Lean',retained_key_mode='0600',source_directories_unchanged=True)
(E/'NCR_VALIDATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
