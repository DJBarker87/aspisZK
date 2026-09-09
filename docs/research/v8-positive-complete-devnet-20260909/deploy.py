#!/usr/bin/env python3
"""Deploy only the named fresh experiment, with explicit retained buffer keys."""
import hashlib, json, os, subprocess, sys, time
import devnet as d

assert os.environ.get('ASPIS_RPC_PROVIDER') == 'helius'
name=sys.argv[1]
assert name=='verifier', 'Pool and Registry are authenticated unchanged, never redeployed here.'
gate=json.loads((d.HERE/'evidence/local-gate.json').read_text());assert gate['local_complete_passed']
assert hashlib.sha256(d.artifact('verifier').read_bytes()).hexdigest()==gate['verifier_sha256']
assert name in ['verifier','pool','registry']
assert d.rpc('getGenesisHash',[])==d.GENESIS
elf=d.artifact(name)
hashes=json.loads((d.HERE/'elf-hashes.json').read_text())
assert hashlib.sha256(elf.read_bytes()).hexdigest()==hashes[name]
program=d.rpc('getAccountInfo',[d.IDS[name],{'encoding':'base64','commitment':'finalized'}])['value']
assert program is None, 'Existing program: authenticate it separately; this command never upgrades.'
configuration=d.PRIVATE/'devnet-cli.yml'
configuration.write_text('---\njson_rpc_url: '+json.dumps(d.RPC)+'\nwebsocket_url: ""\nkeypair_path: '+json.dumps(str(d.key_path('payer')))+'\naddress_labels: {}\ncommitment: finalized\n')
configuration.chmod(0o600)
args=['solana','program','deploy','--config',str(configuration),'--keypair',str(d.key_path('payer')),
      '--program-id',str(d.key_path(name)),'--buffer',str(d.key_path(name+'_buffer')),
      '--max-len',str(elf.stat().st_size),'--upgrade-authority',str(d.key_path('payer')),'--use-rpc','--max-sign-attempts','2','--with-compute-unit-price','1000','--output','json',str(elf)]
stamp=str(time.time_ns());log=d.EVIDENCE/(name+'-deploy-'+stamp+'.log')
d.save(log.with_suffix('.command.json'),{'argv':args,'rpc_provider':'Helius devnet','explicit_buffer_key_retained':True})
t=time.monotonic()
with log.open('w') as f:
    process=subprocess.Popen(args,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,text=True,env={**os.environ,'NO_DNA':'1'})
    for line in process.stdout:
        line=line.replace(d.RPC,'[Helius devnet]').replace(d.RPC_SECRET,'[REDACTED]')
        f.write(line);f.flush();print(line,end='',flush=True)
    code=process.wait()
d.save(log.with_suffix('.status.json'),{'exit_status':code,'wall_seconds':time.monotonic()-t,'keys_retained':True})
raise SystemExit(code)
