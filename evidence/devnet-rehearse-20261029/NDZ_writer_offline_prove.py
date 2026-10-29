"""Offline writer environment probe; mounts no devnet key and disables networking."""
import hashlib,json,pathlib,subprocess,time
E=pathlib.Path(__file__).resolve().parent;keys=E/'keys';private=keys/'NDZ_writer_offline';private.mkdir(mode=0o700,exist_ok=False)
image='sha256:a5fd19592cef47ad41bf1891997e324febf21a442cc71fac4eaf77877d60562a'
command=['docker','run','--rm','--network','none','--platform','linux/amd64','--memory','4g','--memory-swap','4g','--cpus','4','--pids-limit','256','--user',str(__import__('os').getuid())+':'+str(__import__('os').getgid()),'--read-only','--tmpfs','/tmp:rw,size=64m','--cap-drop','ALL','--security-opt','no-new-privileges','--mount',f'type=bind,source={E},target={E},readonly','--mount',f'type=bind,source={keys},target={keys}',image,'python3','-c']
inner=r'''
import hashlib,json,os,pathlib,subprocess,sys,time
E=pathlib.Path(sys.argv[1]);root=E/'keys/NDZ_writer_offline';os.umask(0o077);public=[]
for i in range(8):
 p=root/('attempt-'+str(i)+'.json')
 subprocess.run(['/opt/aspis/cli/solana-keygen','new','--no-bip39-passphrase','--silent','-o',str(p)],stdout=subprocess.DEVNULL,check=True)
 os.chmod(p,0o600)
 pub=subprocess.check_output(['/opt/aspis/cli/solana-keygen','pubkey',str(p)],text=True).strip();public.append({'path':str(p),'public':pub,'mode':'0600'})
q=json.load(open(E/'NDZ_writer-proof-public-input.json'));q['proof_accounts']=[r['public'] for r in public];q['proof_dir']=str(root/'proof')
start=time.monotonic();p=subprocess.run(['timeout','900','/opt/aspis/devnet_spend'],input=json.dumps(q),text=True,capture_output=True)
(root/'result.json').write_text(p.stdout);(root/'stderr.txt').write_text(p.stderr)
result={'exit':p.returncode,'wall_seconds':time.monotonic()-start,'keys_public':public,'network':'none','devnet_key_mounts':0,'signatures_generated':0,'expected_time':'one optimized selected64 proof-generation call; no compilation','limits':{k:pathlib.Path('/sys/fs/cgroup/'+k).read_text().strip() for k in ['memory.max','memory.swap.max','memory.peak','memory.swap.peak']},'client_sha256':hashlib.sha256(pathlib.Path('/opt/aspis/devnet_spend').read_bytes()).hexdigest()}
if p.returncode==0:
 plan=json.loads(p.stdout);assert plan['p_r1'] and plan['client_route']=='selected64-proof-account-v1';result.update(attempts=plan['attempts'],attempt_index=plan['attempt_index'],proof_bytes=plan['proof_bytes'],artifacts={name:hashlib.sha256((root/'proof'/name).read_bytes()).hexdigest() for name in ['proof.bin','statement.bin']})
(root/'public-result.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2));raise SystemExit(p.returncode)
'''
(E/'NDZ_WRITER_PROVE_LAUNCH.json').write_text(json.dumps({'command':command+['<embedded public probe script>',str(E)],'expected_time':'one optimized selected64 proof-generation call under emulation','network':'none','memory_max':4294967296,'memory_swap_max':0,'private_directory_retained':str(private),'devnet_key_mounts':0},indent=2)+'\n')
start=time.monotonic();result=subprocess.run(command+[inner,str(E)],capture_output=True,text=True)
(E/'NDZ_writer-offline-prove.log').write_text(result.stdout+result.stderr)
assert result.returncode==0,result.stderr
public=json.loads((private/'public-result.json').read_text());public['launcher_wall_seconds']=time.monotonic()-start;public['image_id']=image
(E/'NDZ_WRITER_PROVE_RESULT.json').write_text(json.dumps(public,indent=2)+'\n');print(json.dumps(public,indent=2))
