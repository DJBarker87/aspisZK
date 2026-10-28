import pathlib,subprocess,json,sys,hashlib,os
D=pathlib.Path('/home/dombarker/project-offloads/codex-pv-fscan-20261028');S=D/'src';name=sys.argv[1]
configs={'client':('tools/r1-cost-probe/Cargo.toml','r1p-check,aspis-r1-cost-probe/ct-host-prover',None),'default':('programs/r1-cost-probe/Cargo.toml','pool-adapter,private-leaf-salts','aspis-r1-cost-probe-program'),'devnet':('programs/r1-cost-probe/Cargo.toml','pool-adapter,private-leaf-salts','aspis-r1-cost-probe-program'),'pool':('programs/aspis-pool/Cargo.toml','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit','aspis-pool')}
m,f,p=configs[name];out=D/('config-'+name);out.mkdir(exist_ok=True)
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],RUSTUP_TOOLCHAIN='1.94.1',CARGO_BUILD_JOBS='4')
cmd=['cargo','metadata','--format-version','1','--locked','--manifest-path',str(S/m),'--features',f]
r=subprocess.run(cmd,env=env,capture_output=True,text=True);(out/'stderr.log').write_text(r.stderr);(out/'command.json').write_text(json.dumps(cmd));print(r.stderr[-3000:]);
if r.returncode:sys.exit(r.returncode)
a=json.loads(r.stdout);(out/'metadata.json').write_text(r.stdout);pk={x['id']:x for x in a['packages']};b=[dict(name=pk[x['id']]['name'],version=pk[x['id']]['version'],id=x['id'],features=x['features']) for x in a['resolve']['nodes']];(out/'features.json').write_text(json.dumps(b,indent=2));print(json.dumps([x for x in b if x['name'].startswith('aspis')],indent=2))
