#!/usr/bin/env python3
"""Deploy pinned artifacts with retained buffers; run in the host receipt scope."""
import hashlib,json,os,pathlib,subprocess,sys,time,urllib.request
cfg=json.load(open(sys.argv[1]));out=pathlib.Path(sys.argv[2]);out.mkdir(exist_ok=False,mode=0o700)
cli=pathlib.Path.home()/'.local/share/solana/install/active_release/bin'
def rpc(method,params):
    req=urllib.request.Request(cfg['rpc_url'],json.dumps(dict(jsonrpc='2.0',id=1,method=method,params=params)).encode(),{'Content-Type':'application/json'})
    with urllib.request.urlopen(req,timeout=90) as r: v=json.load(r)
    if 'error' in v: raise RuntimeError(v['error'])
    return v['result']
results={}
for role in ['verifier','pool','registry']:
    artifact=cfg['release_artifacts']['devnet_verifier' if role=='verifier' else role]
    data=pathlib.Path(artifact['path']).read_bytes();assert hashlib.sha256(data).hexdigest()==artifact['sha256']
    before=rpc('getAccountInfo',[cfg['programs'][role],{'commitment':'finalized','encoding':'base64'}])
    (out/(role+'-before.json')).write_text(json.dumps(before,indent=2))
    if before['value'] is not None: raise RuntimeError(f'{role} exists; inspect before redeployment')
    buffer=pathlib.Path('keys')/(role+'-deploy-buffer.json')
    if not buffer.exists():
        subprocess.run([str(cli/'solana-keygen'),'new','--no-bip39-passphrase','--silent','-o',str(buffer)],stdout=subprocess.DEVNULL,check=True)
    os.chmod(buffer,0o600)
    cmd=[str(cli/'solana'),'--url',cfg['rpc_url'],'--keypair','keys/payer.json','--commitment','finalized','--output','json','program','deploy',artifact['path'],'--program-id',f'keys/{role}.json','--buffer',str(buffer),'--max-len',str(len(data)),'--use-rpc','--max-sign-attempts','10']
    (out/(role+'-command.json')).write_text(json.dumps(cmd))
    t=time.monotonic()
    with open(out/(role+'-deploy.json'),'w') as stdout,open(out/(role+'-stderr.txt'),'w') as stderr:
        p=subprocess.run(cmd,stdout=stdout,stderr=stderr)
    results[role]={'exit':p.returncode,'wall_seconds':time.monotonic()-t,'sha256':artifact['sha256'],'bytes':len(data)}
    (out/'results.json').write_text(json.dumps(results,indent=2))
    if p.returncode: sys.exit(p.returncode)
    account=rpc('getAccountInfo',[cfg['programs'][role],{'commitment':'finalized','encoding':'base64'}]);(out/(role+'-after.json')).write_text(json.dumps(account,indent=2))
    print(role,json.dumps(results[role]),flush=True)
