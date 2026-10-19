from pathlib import Path
import hashlib,json,subprocess,time,struct
W=Path('/home/dombarker/project-offloads/aspis-r1-decision1g-20261018'); O=W/'elf-audit-inputs';O.mkdir(exist_ok=False)
B=Path('/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin'); linked=W/'sbf-target/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so'; stripped=W/'artifacts/aspis_r1_cost_probe_program.so'; log=W/'runs/sbf-build-1g-fallback/stdout.log'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
commands=[]
def run(name,argv,stdin=None):
 out=O/(name+'.log');err=O/(name+'.stderr.log');metrics=O/(name+'.time.log');start=time.monotonic()
 with out.open('wb')as f,err.open('wb')as e:code=subprocess.run(['/usr/bin/time','-v','-o',str(metrics),*map(str,argv)],input=stdin,stdout=f,stderr=e).returncode
 commands.append({'name':name,'argv':list(map(str,argv)),'exit':code,'wall_seconds':time.monotonic()-start,'time_log':str(metrics),'stdout':str(out),'stderr':str(err)});return out
for tag,path in [('linked',linked),('stripped',stripped)]:
 for name,flags in [('symbols',['--symbols','--wide']),('dynsym',['--dyn-syms','--wide']),('relocations',['--relocations','--wide']),('sections',['--sections','--wide'])]:run(tag+'-'+name,[B/'llvm-readelf',*flags,path])
 run(tag+'-disassembly',[B/'llvm-objdump','-d','-r','--no-show-raw-insn',path])
 if (B/'llvm-nm').exists():
  nm=run(tag+'-nm',[B/'llvm-nm','--no-demangle','--numeric-sort','--print-size',path])
  if(B/'llvm-cxxfilt').exists():run(tag+'-demangled',[B/'llvm-cxxfilt'],nm.read_bytes())
def text_info(path):
 data=path.read_bytes();assert data[:6]==b'\x7fELF\x02\x01';off=struct.unpack_from('<Q',data,40)[0];size,num,strings=struct.unpack_from('<HHH',data,58);secs=[struct.unpack_from('<IIQQQQIIQQ',data,off+i*size)for i in range(num)];s=secs[strings];names=data[s[4]:s[4]+s[5]]
 for sec in secs:
  name=names[sec[0]:].split(b'\0',1)[0]
  if name==b'.text':return {'address':sec[3],'offset':sec[4],'bytes':sec[5],'sha256':hashlib.sha256(data[sec[4]:sec[4]+sec[5]]).hexdigest()}
 raise ValueError('no text')
records=[];unknown=[]
for n,line in enumerate(log.read_text().splitlines(),1):
 if line.startswith('Error:'):
  import re
  symbol=re.search(r'(?:Function |function call in method )(\S+)',line);nums=[int(x)for x in re.findall(r'Stack offset(?: of)? (\d+)',line)];frames=[int(x)for x in re.findall(r'Estimated function frame size: (\d+)',line)];overwrite='overwrites values in the frame'in line
  d={'line':n,'raw':line,'symbol':symbol.group(1)if symbol else None,'offsets':nums,'frames':frames,'overwrite':overwrite};records.append(d)
  if not symbol or not(nums or frames or overwrite):unknown.append(d)
(O/'warning-inventory.json').write_text(json.dumps({'diagnostics':records,'unparsed':unknown},indent=2)+'\n')
info={'revision':'910cb693a77fe973ae385af868891fe3d09a3676','features':['pool-adapter','private-leaf-salts'],'linked':{'path':str(linked),'sha256':sha(linked),'bytes':linked.stat().st_size,'text':text_info(linked)},'stripped':{'path':str(stripped),'sha256':sha(stripped),'bytes':stripped.stat().st_size,'text':text_info(stripped)},'raw_build_log':{'path':str(log),'sha256':sha(log)},'commands':commands,'tools':{str(B/n):sha(B/n)for n in ['llvm-readelf','llvm-objdump','llvm-nm','llvm-cxxfilt']if(B/n).exists()},'capture_source_sha256':sha(__file__),'outputs':{p.name:sha(p)for p in O.iterdir()if p.is_file()}}
(O/'input.json').write_text(json.dumps(info,indent=2)+'\n');print(json.dumps({'commands':[(c['name'],c['exit'])for c in commands],'linked':info['linked'],'stripped':info['stripped'],'diagnostics':len(records),'unparsed':len(unknown)},indent=2))
