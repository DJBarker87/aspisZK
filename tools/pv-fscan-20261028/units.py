import pathlib,subprocess,json,os,sys
D=pathlib.Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');S=D/'src';name=sys.argv[1];m,f,p,t={'client':('tools/r1-cost-probe/Cargo.toml','r1p-check,aspis-r1-cost-probe/ct-host-prover','aspis-r1-cu-probe','1.94.1'),'default':('programs/r1-cost-probe/Cargo.toml','pool-adapter,private-leaf-salts','aspis-r1-cost-probe-program','1.89.0-sbpf-solana-v1.52'),'devnet':('programs/r1-cost-probe/Cargo.toml','pool-adapter,private-leaf-salts','aspis-r1-cost-probe-program','1.89.0-sbpf-solana-v1.52'),'pool':('programs/aspis-pool/Cargo.toml','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit','aspis-pool','1.89.0-sbpf-solana-v1.52')}[name]
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN=t,RUSTC_BOOTSTRAP='1')
cmd=['cargo','build','--release','--locked','--manifest-path',str(S/m),'-p',p,'--features',f,'-j','4','-Z','unstable-options','--unit-graph']
if name!='client':cmd+=['--target','sbpf-solana-solana']
O=D/('units-'+name);O.mkdir(exist_ok=True);(O/'command.json').write_text(json.dumps(dict(argv=cmd,toolchain=t),indent=2));r=subprocess.run(cmd,env=env,capture_output=True,text=True);(O/'stderr.log').write_text(r.stderr);print(r.stderr[-2000:]);
if r.returncode:sys.exit(r.returncode)
a=json.loads(r.stdout);(O/'unit-graph.json').write_text(r.stdout)
meta=json.loads((D/('config-'+name)/'metadata.json').read_text());pk={x['id']:x for x in meta['packages']}
b=[dict(package_id=u['pkg_id'],name=pk.get(u['pkg_id'],{}).get('name',u['pkg_id']),features=u['features'],profile=u['profile'],platform=u['platform'],target=u['target']) for u in a['units']];(O/'features.json').write_text(json.dumps(b,indent=2));print('units',len(b));print(json.dumps([x for x in b if x['name'].startswith('aspis')],indent=2)[-6000:])
