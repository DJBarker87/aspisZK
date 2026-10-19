from pathlib import Path
import hashlib,json,subprocess,shutil,time
W=Path('/home/dombarker/project-offloads/aspis-r1-j1a-readonly-account-20261016')
CACHE=Path('/home/dombarker/project-offloads/aspis-r1-j1a-terminal-20261016/native-target')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1024*1024),b''):h.update(c)
 return h.hexdigest()
def dump(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
pins=json.loads((W/'tool-pins.json').read_text())
for row in pins['tools'].values():assert sha(Path(row['path']))==row['sha256'],row['path']
for path,h in pins['rust_runtime_binaries'].items():assert sha(Path(path))==h,path
sdk=[]
for row in json.loads((W/'sdk-source-pins.json').read_text()):
 path=Path(row['source_path'].replace('/Users/dominic/.cargo/registry/src/','/home/dombarker/.cargo/registry/src/'))
 assert sha(path)==row['source_sha256'],str(path)
 sdk.append({**row,'actual_host_path':str(path)})
units=subprocess.check_output(['systemctl','--user','list-units','--type=scope','--state=running','--no-pager','--plain','--no-legend'],text=True)
scopes={}
for line in units.splitlines():
 unit=line.split()[0]
 scopes[unit]=subprocess.check_output(['systemctl','--user','show',unit,'-p','MemoryHigh','-p','MemoryMax','-p','MemorySwapMax','-p','MemoryCurrent'],text=True)
proc=subprocess.check_output(['ps','-eo','pid,ppid,rss,comm'],text=True)
active=[l for l in proc.splitlines() if any(x in l.split()[-1:] for x in ['lean','rustc','cargo','charon','charon-driver','aeneas'])]
dump(W/'reservation-inventory.json',{'time_unix':time.time(),'scope_limits':scopes,'active_build_processes':active,'communicated_reservations':{'B':8*2**30,'C_maximum':8*2**30,'A':0,'root':0},'sum_memorymax_upper_bound':16*2**30,'safe_limit':48*2**30,'free':subprocess.check_output(['free','-b'],text=True)})
assert not any((W/'native-target').iterdir()),'Do not replace an existing task cache'
subprocess.run(['cp','-a','--reflink=auto',str(CACHE)+'/.' ,str(W/'native-target')],check=True)
shutil.copy2(W/'Cargo.lock.seed',W/'input/Cargo.lock')
dump(W/'preflight.json',{'sdk_files_verified':sdk,'tools_match_retained_pins':True,'native_cache_origin':str(CACHE),'origin_rustc_info_sha256':sha(CACHE/'.rustc_info.json'),'copied_rustc_info_sha256':sha(W/'native-target/.rustc_info.json'),'copy_mode':'cp -a --reflink=auto; private destination, no hardlink sharing requested','source_revision':'b2ad6649de4c1b97c2270a1c8bd4bbfe5537d52c','production_changed':False})
print('Verified three tool binaries, Rust runtime binaries and five real SDK source files; copied private matching-nightly cache')
