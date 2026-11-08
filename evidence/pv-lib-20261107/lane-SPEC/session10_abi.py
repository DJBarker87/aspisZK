"""Read-only adopted ELF/site inventory and frozen source type projection."""
import pathlib,subprocess,hashlib,json,lzma,sys
L=pathlib.Path(__file__).resolve().parent
REV='41e76d01fdead952101594b8b0f36a7561d180f2'
PATH='evidence/pv-evhB-20261103/thread-line/generated/N95807/OrderedFamilies.llbc.xz'
raw=lzma.decompress(subprocess.check_output(['git','show',REV+':'+PATH])); r=json.loads(raw)['translated']
assert r['target_information']==[{'key':'x86_64-unknown-linux-gnu','value':{'target_pointer_size':8,'is_little_endian':True}}]
types={str(i):r['type_decls'][i] for i in [21,22,23,58,68,78,79,112,133]}
expected={22:['num_running_threads','a_thread_panicked','main_thread'],68:['strong','weak','data'],79:['name','id','parker'],112:['scope','result','_marker'],133:['handle','rust_start']}
for i,fields in expected.items():assert [f['name'] for f in types[str(i)]['kind']['Struct']]==fields
binary='/home/dombarker/project-offloads/codex-pv-uc-20261029/native-target/client/user_client'
commands=[['sha256sum',binary],['objdump','--version'],['readelf','-rW',binary]]
cuts=[(0xfa060,0xfa0d2),(0xe0450,0xe066f),(0x17be40,0x17bf19),(0x1a6720,0x1a675d),(0x17c480,0x17c512)]
commands += [['objdump','-d',f'--start-address={a}',f'--stop-address={b}',binary] for a,b in cuts]
if '--check' not in sys.argv:
 script='import subprocess,json\ncommands='+repr(commands)+'\nprint(json.dumps([subprocess.check_output(c,text=True) for c in commands]))'
 outputs=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3 - <<\'REMOTE\'\n'+script+'\nREMOTE'],text=True))
 assert outputs[0].split()[0]=='fc8808eb454f3156dba550140398cc3a74af4c88ee5b3491d2d04d33ee904558'
 # Retain only relevant relocations, not the entire binary's relocation table.
 outputs[2]='\n'.join(line for line in outputs[2].splitlines() if any(a in line for a in ['1b3758','1b3750','1b3720','1b3760','1b41c0']))+'\n'
 (L/'SESSION10_ABI_BINARY.txt').write_text('\n'.join(outputs))
b=(L/'SESSION10_ABI_BINARY.txt').read_text()
for site in ['fa099:','fa0ce:','e058a:','e05e8:','e064b:','17be96:','17bedc:','17bef7:','1a6720','17c4a1:']:assert site in b,site
report={'source_revision':REV,'source_path':PATH,'llbc_sha256':hashlib.sha256(raw).hexdigest(),'target':r['target_information'],'types':types,'binary_sha256':b.split()[0],
 'evidence_class':'binary-structural (adopted binary), plus V370 compiler-cohort',
 'sites':[
 {'allocation':'ScopeData ArcInner','width':40,'align':8,'call':'fa099','stores':{'0:8':'fa0b3=1','8:16':'fa0ba=1','16:24':'fa0c2=current Thread pointer r14','24:32':'fa0c6=0','32:33':'fa0ce=0'},'holes':[[33,40]]},
 {'allocation':'Packet ArcInner','width':48,'align':8,'call':'e058a','stores':{'0:8':'e059c=1','8:16':'e05a3=1','16:24':'e05ab=scope pointer r14','24:32':'e05b3=2^63+2'},'holes':[[32,48]]},
 {'allocation':'callback Box','width':56,'align':8,'call':'e05e8','stores':{'0:16':'e0619=bytes rsp+0x38','16:32':'e0614=bytes rsp+0x48','32:40':'e061d=Packet pointer r12','40:48':'e0621=capture pointer rcx','48:56':'e0625=capture length rax'},'holes':[],'copied_padding':'preserve actual source bytes, including unknowns; no serializer zeros'},
 {'allocation':'ThreadInit Box','width':24,'align':8,'call':'e064b','stores':{'0:8':'e065a=handle r13','8:16':'e065d=callback pointer r14','16:24':'e0668=relocated vtable'},'holes':[]},
 {'allocation':'thread::Thread::new ArcInner<Inner>','width':48,'align':8,'call':'17be96','source_caller':'e0541 -> GOT1b3758 ->17be40','layout_calculation':'17be67=8,17be6c=32; GOT1b41c0 ->1a6720 arcinner_layout_for_value_layout returns8/48','stores':{'0:8':'17bedc=1','8:16':'17bee3=1','16:24':'17bef3=ThreadId r15','24:32':'17beeb=name pointer rbx','32:40':'17beef=name length r14 (unconstrained when name absent)','40:44':'17bef7=parker0'},'holes':[[44,48]]}],
 'limits':['Does not assert original-entry reachability or full source/native adequacy.','Current-thread already-initialized TLS path17c49f/17c4a1 has no allocation; uninitialized path17c50a calls the same Thread::new site.','Nonempty name conversion, environment lookup when stack-size cache absent, hook allocation and native backend internals have not been shown absent in one continuous witness. No images or successful trace credit is supplied for them.','Vec buffers follow the requested ThreadInit cut and remain outside this prefix, not silently initialized.']}
p=L/'SESSION10_ABI_SOURCE.json'; content=json.dumps(report,indent=2)+'\n'
if '--check' in sys.argv:assert p.read_text()==content
else:p.write_text(content)
print('PASS: five distinct allocation images; frozen type fields and adopted ELF stores retained')
