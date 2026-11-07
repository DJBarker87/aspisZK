"""Focused PreCodegen MIR/span evidence; verify codegen symbol identity, Pool ELF."""
import pathlib,json,sys,hashlib,subprocess,os,time,re,lzma,shutil
B=pathlib.Path(__file__).resolve().parent;a=sys.argv[1];c={'PCH_B004':'aspis_core','PCH_B005':'aspis_statement','PCH_B006':'aspis_pool'}[a];out=B/a;out.mkdir(exist_ok=False);dump=out/'mir';dump.mkdir()
assert shutil.disk_usage(B).free>=40_000_000_000
if c=='aspis_pool':cmd=json.loads((B/'PCH_B003_BUILD.json').read_text())['command'];base=B/'PCH_B003/aspis_pool.ll'
else:
 rec=json.loads((B/'PCH_B002_DEPENDENCIES.json').read_text());cmd=next(r['command'] for r in rec['commands'] if r['crate']==c);base=next((B/'PCH_B002').glob(c+'-*.ll'))
cmd=cmd[:];cmd[cmd.index('--out-dir')+1]=str(out);cmd+=['-Zdump-mir=PreCodegen','-Zdump-mir-dir='+str(dump),'-Zmir-include-spans=yes']
env=os.environ.copy();env.update(OUT_DIR=str(B/'core-out'),CARGO_NET_OFFLINE='true')
t=time.monotonic()
with (out/'stdout').open('w') as o,(out/'stderr').open('w') as e:r=subprocess.run(cmd,cwd=B/'src',env=env,stdout=o,stderr=e)
rec=dict(attempt=a,crate=c,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-t,expected_work='optimized compilation for previously missing source-span/PreCodegen evidence',lock_sha256=hashlib.sha256((B/'src/Cargo.lock').read_bytes()).hexdigest())
if r.returncode==0:
 f=next(out.glob('*.ll'));symbols=lambda p:sorted(re.findall(r'^define[^\n]*?@("[^"]+"|[-\w.$]+)\(',p.read_text(),re.M));rec['same_codegen_symbols']=symbols(f)==symbols(base);assert rec['same_codegen_symbols']
 if c=='aspis_pool':
  r2=subprocess.run(['/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin/llvm-objcopy','--strip-all',str(out/'aspis_pool.so'),str(out/'aspis_pool.stripped.so')],capture_output=True,text=True);assert r2.returncode==0,r2.stderr
  rec['elf_sha256']=hashlib.sha256((out/'aspis_pool.stripped.so').read_bytes()).hexdigest();assert rec['elf_sha256']=='e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc'
 payload={p.name:p.read_text() for p in sorted(dump.glob('*.mir'))};raw=json.dumps(payload,sort_keys=True).encode();(B/(a+'_MIR_DUMP.json.xz')).write_bytes(lzma.compress(raw));(B/(a+'_MIR_DUMP.json.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');rec['dump_files']=len(payload);rec['dump_raw_bytes']=len(raw);rec['dump_sha256']=hashlib.sha256(raw).hexdigest()
 for p in [f,*out.glob('*.mir'),out/'stdout',out/'stderr']:
  (B/(a+'_'+p.name+'.xz')).write_bytes(lzma.compress(p.read_bytes()))
(B/(a+'_DUMP.json')).write_text(json.dumps(rec,indent=1))
print('PCH PreCodegen '+c+': exit '+str(r.returncode)+'; files '+str(rec.get('dump_files')))
assert r.returncode==0
