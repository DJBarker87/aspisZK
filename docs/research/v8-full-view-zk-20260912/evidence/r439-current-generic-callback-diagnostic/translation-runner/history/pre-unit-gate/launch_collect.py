#!/usr/bin/env python3
"""Fail-closed R439 Aeneas translator launcher/collector; prepared but not launched."""
import argparse, datetime, hashlib, json, pathlib, shlex, subprocess, tarfile, io, sys
HERE=pathlib.Path(__file__).resolve().parent
WORKTREE=pathlib.Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
HOST='dombarker@100.108.41.90'
SSH_OPTS=['-o','BatchMode=yes','-o','ConnectTimeout=5','-o','StrictHostKeyChecking=no','-o','UserKnownHostsFile=/dev/null']
BINARY='/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a/aeneas-r425-unit-constant-candidate'
BINARY_SHA256='eadb205fc1e00cf7e32197dd7cbbbd82aa42b59442d8f186cfdca7c8fdca9b01'
NAMESPACE='AspisR439GenericGamma'
REMOTE_INPUT='/home/dombarker/project-offloads/aspis-r439-generic-gamma-20261003-a/input/R439Input.llbc'
REMOTE_OUTPUT='/home/dombarker/project-offloads/aspis-r439-generic-gamma-20261003-a/translation'
WORKROOT='/home/dombarker/project-offloads/aspis-r20-r117-primal-20260930-a'
UNIT='aspis-r439-generic-gamma-translation'
CAPS={'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':'0','TasksMax':128,'RuntimeMaxSec':'600s'}
LEAD_APPROVAL=HERE/'lead-input-approval.json'
OUTPUTS=HERE/'output'

def sha_bytes(b): return hashlib.sha256(b).hexdigest()
def sha(p): return sha_bytes(pathlib.Path(p).read_bytes())
def run(argv, **kwargs): return subprocess.run(argv,check=True,**kwargs)
def remote(argv): return run(['ssh',*SSH_OPTS,HOST,shlex.join(argv)])
def checked_capture(argv): return subprocess.check_output(argv,text=True).strip()
def load_approval():
    assert LEAD_APPROVAL.is_file(), f'missing lead-reviewed input approval: {LEAD_APPROVAL}'
    approval=json.loads(LEAD_APPROVAL.read_text())
    assert approval.get('status')=='APPROVED_BY_LEAD'
    local=pathlib.Path(approval['projection_local_path']).resolve()
    expected=approval['projection_sha256']
    assert len(expected)==64 and all(c in '0123456789abcdef' for c in expected)
    assert local.is_file() and sha(local)==expected
    llbc=json.loads(local.read_text())
    assert llbc.get('has_errors') is False
    tr=llbc['translated']; assert len(tr['fun_decls'])>284
    root=tr['fun_decls'][284]; src=root.get('src',{}).get('TraitImpl',{})
    assert src.get('impl_ref',{}).get('id')==47
    assert src.get('trait_ref',{}).get('id')==9
    assert src.get('item_id')=={'Method':0} and src.get('reuses_default') is False
    assert len(tr['trait_impls'])>47 and tr['trait_impls'][47].get('impl_trait',{}).get('id')==9
    assert approval.get('expected_native_root_fun_id')==284
    assert approval.get('expected_namespace')==NAMESPACE
    assert approval.get('expected_impl_id')==47
    assert approval.get('expected_trait_id')==9
    assert approval.get('expected_method_id')==0
    assert approval.get('expected_source_revision')==checked_capture(['git','rev-parse','HEAD'],cwd=WORKTREE)
    projection_rev=approval.get('projection_source_revision')
    assert isinstance(projection_rev,str) and len(projection_rev)==40 and all(c in '0123456789abcdef' for c in projection_rev)
    return approval,local,expected

def safe_extract(tarbytes,dest):
    dest.mkdir(parents=True,exist_ok=False)
    with tarfile.open(fileobj=io.BytesIO(tarbytes),mode='r:gz') as tf:
        members=tf.getmembers()
        for m in members:
            p=pathlib.PurePosixPath(m.name)
            assert not p.is_absolute() and '..' not in p.parts and (m.isfile() or m.isdir()),m.name
        tf.extractall(dest,filter='data')

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--prepare-only',action='store_true'); ap.add_argument('--launch',action='store_true'); args=ap.parse_args()
    assert args.prepare_only ^ args.launch, 'choose exactly one mode'
    if args.prepare_only:
        print(json.dumps({'status':'PREPARED_NOT_LAUNCHED','binary_sha256':BINARY_SHA256,'input':'pending lead projection path/SHA','namespace':NAMESPACE,'target_native_fun_id':284,'target_impl_id':47,'target_trait_id':9,'target_method_id':0,'caps':CAPS},indent=2))
        return 0
    approval,local_input,input_sha=load_approval()
    assert OUTPUTS.is_dir() or not OUTPUTS.exists()
    revision=checked_capture(['git','rev-parse','HEAD'],cwd=WORKTREE)
    assert revision==approval['expected_source_revision']
    script=HERE/'remote_translate.py'; script_bytes=script.read_bytes(); script_sha=sha_bytes(script_bytes)
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    run_id=f'{revision[:12]}-{stamp}'; hist=HERE/'launch-history'/run_id
    hist.mkdir(parents=True,exist_ok=False)
    out=OUTPUTS/run_id
    facts={'remote_input':REMOTE_INPUT,'remote_output':REMOTE_OUTPUT,'binary':BINARY,'binary_sha256':BINARY_SHA256,'input_sha256':input_sha,'source_revision':revision,'namespace':NAMESPACE,'caps':CAPS,'expected_root_fun_id':284,'expected_impl_id':47,'expected_trait_id':9,'expected_method_id':0,'input_source_revision':approval['projection_source_revision']}
    systemd=['systemd-run','--user','--wait','--collect','--pipe','--unit='+UNIT,'--working-directory='+WORKROOT,
      '-p','MemoryHigh=5G','-p','MemoryMax=7G','-p','MemorySwapMax=0','-p','TasksMax=128','-p','RuntimeMaxSec=600s',
      '-p','KillMode=control-group','-p','TimeoutStopSec=10s','python3','-c',script_bytes.decode(),json.dumps(facts,separators=(',',':'))]
    ssh_argv=['ssh',*SSH_OPTS,HOST,shlex.join(systemd)]
    record={'status':'LAUNCH_AUTHORIZED_BY_REVIEWED_INPUT','input_local_path':str(local_input),'input_sha256':input_sha,'lead_approval_sha256':sha(LEAD_APPROVAL),'input_remote_path':REMOTE_INPUT,'remote_output':REMOTE_OUTPUT,'binary_path':BINARY,'binary_sha256':BINARY_SHA256,'source_revision':revision,'projection_source_revision':approval['projection_source_revision'],'namespace':NAMESPACE,'expected_root_fun_id':284,'expected_impl_id':47,'expected_trait_id':9,'expected_method_id':0,'caps':CAPS,'systemd_argv':systemd,'ssh_argv':ssh_argv,'remote_payload_sha256':script_sha,'started_at_utc':stamp}
    (hist/'launch.json').write_text(json.dumps(record,indent=2)+'\n')
    # Never overwrite a staged input or existing output tree.
    remote(['test','!','-e',REMOTE_OUTPUT])
    remote(['test','!','-e',REMOTE_INPUT])
    remote(['mkdir','-p',str(pathlib.PurePosixPath(REMOTE_INPUT).parent)])
    run(['scp',*SSH_OPTS,str(local_input),HOST+':'+REMOTE_INPUT])
    remote(['python3','-c','import hashlib,pathlib,sys; p=pathlib.Path(sys.argv[1]); assert hashlib.sha256(p.read_bytes()).hexdigest()==sys.argv[2]',REMOTE_INPUT,input_sha])
    with (hist/'launch.log').open('wb') as log:
        proc=subprocess.run(ssh_argv,stdout=log,stderr=subprocess.STDOUT)
    (hist/'launch-result.json').write_text(json.dumps({'launcher_exit_status':proc.returncode,'launch_revision':revision,'remote_script_sha256':script_sha},indent=2)+'\n')
    collection_stderr=hist/'collection.stderr.log'
    tarcmd=['tar','-czf','-','-C',REMOTE_OUTPUT,'.']
    cp=subprocess.run(['ssh',*SSH_OPTS,HOST,shlex.join(tarcmd)],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    collection_stderr.write_bytes(cp.stderr)
    (hist/'collection-status.json').write_text(json.dumps({'exit_status':cp.returncode,'tar_bytes':len(cp.stdout),'tar_sha256':sha_bytes(cp.stdout)},indent=2)+'\n')
    if cp.returncode==0: safe_extract(cp.stdout,out)
    record.update({'launcher_exit_status':proc.returncode,'collection_exit_status':cp.returncode,'local_output':str(out) if cp.returncode==0 else None})
    (hist/'launch.json').write_text(json.dumps(record,indent=2)+'\n')
    return proc.returncode or cp.returncode

if __name__=='__main__': raise SystemExit(main())
