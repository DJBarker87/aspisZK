import hashlib,json,pathlib,resource,subprocess,sys,time
root=pathlib.Path('/Users/dominic/ZK/.worktrees/r1-lead-followup-20261016')
base='docs/research/100bit-spend-path-20261013'
folder=root/base/'evidence/verify-query-followup-integration-20261017'
revision=subprocess.check_output(['git','-C',str(root),'rev-parse','HEAD'],text=True).strip()
script=base+'/tools/j1-integrated-declaration-repin.py'
command=[sys.executable,script,'--revision',revision,'--migration-before','85ef4199b']
for name in ['opening-queries-current-20261017/registered-cones.json','verify-helper-prefix-fe80-20261017/additional-cone.json','semantic-rounds-current-20261017/registered-cones.json','finish-actual25-a555-20261017/additional-cone.json']:
 command+=['--additional-cone',base+'/evidence/'+name]
command+=['--output',str(folder/'declaration-repin.json'),'--require-complete']
start=time.monotonic()
with (folder/'declaration-repin.log').open('wb') as log:
 result=subprocess.run(command,cwd=root,stdout=log,stderr=subprocess.STDOUT)
r=resource.getrusage(resource.RUSAGE_CHILDREN)
receipt={'target':script,'command':command,'source_revision':revision,'checker_sha256':hashlib.sha256((root/script).read_bytes()).hexdigest(),'exit_status':result.returncode,'wall_seconds':time.monotonic()-start,'peak_rss_bytes':r.ru_maxrss*(1 if sys.platform=='darwin' else 1024),'process_swaps':r.ru_nswap,'print_axioms':'N/A (read/hash-only inventory)','builds_executed':False,'log_sha256':hashlib.sha256((folder/'declaration-repin.log').read_bytes()).hexdigest(),'runner_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
(folder/'declaration-repin-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));sys.exit(result.returncode)
