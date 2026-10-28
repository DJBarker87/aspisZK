import pathlib,json,subprocess,re,hashlib,tomllib,tarfile
E=pathlib.Path(__file__).parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def g(p):return subprocess.check_output(['git','show','HEAD:'+p])
samples=json.loads((E/'NCR_RECEIPT_SAMPLE.json').read_text())
for s in samples:
 c=s['receipt'].get('native_command',s['receipt']['command']);s['effective_command']=c
 if not any(x=='kani' or x.endswith('/cargo-kani') or x.endswith('/kani-driver') for x in c):
  p=s['path'].replace('receipt.json','stdout.log')
  try:b=g(p)
  except subprocess.CalledProcessError:continue
  for l in b.decode(errors='replace').splitlines():
   if l.startswith('{'):
    try:j=json.loads(l)
    except ValueError:continue
    a=j.get('command',j.get('kani_command'))
    if isinstance(a,list) and any(x=='kani' or x.endswith('/cargo-kani') or x.endswith('/kani-driver') for x in a):s['effective_command']=a;break
(E/'NCR_RECEIPT_SAMPLE.json').write_text(json.dumps(samples,indent=2)+'\n')
records=[];cache={};pins={}
for lane,path in [('TX1','evidence/native-inv1-20261027/NBI1_INVENTORY.json'),('TX2','evidence/native-inv2-20261027/NBI2_INVENTORY.json')]:
 inv=json.load(open(path))
 for f in inv['functions']:
  p=f['file'];b=cache.setdefault(p,subprocess.check_output(['git','show',rev+':'+p]));pins[p]=hashlib.sha256(b).hexdigest()
  lo,hi=f.get('body_byte_range',[f.get('body_start_byte'),f.get('body_end_byte')]);assert hashlib.sha256(b[lo:hi]).hexdigest()==f['body_sha256']
  body=b[lo:hi].decode();lines=b.decode().splitlines();bl=b[:lo].count(b'\n')+1
  hits=[dict(line=bl+i,text=l) for i,l in enumerate(body.splitlines()) if re.search(r'cfg[!(]|#\[cfg|debug_assert|target_os|target_arch|target_pointer|unsafe|align_of|size_of|transmute|read_unaligned',l)]
  if hits:records.append(dict(lane=lane,file=p,name=f['name'],start=f['line'],end=f['end_line'],hits=hits))
(E/'NCR_BODY_SCAN.json').write_text(json.dumps(dict(revision=rev,inventory_entries=587,unique_files=pins,hits=records),indent=2)+'\n')
manifest=json.load(open('evidence/lowering2-20261026/Low2_build_manifest.json'))
release=[]
for b in manifest['builds']:
 for c in b['compiler_invocations']:
  if c['crate'].endswith('.command'):
   a=c['args'];release.append(dict(mode=b['mode'],crate=c['crate'],codegen_cfg_target=[a[i+1] for i,v in enumerate(a[:-1]) if v in ['--cfg','-C','--target']],compiler=c))
(E/'NCR_RELEASE_CFG.json').write_text(json.dumps(release,indent=2)+'\n')
# Validate local SDK sources against the frozen registry tarball checksums, file by file.
lock=tomllib.loads(subprocess.check_output(['git','show',rev+':Cargo.lock']).decode());sdk=[]
names=['solana-program','solana-sha256-hasher','solana-pubkey','solana-cpi','solana-sysvar','solana-program-entrypoint','solana-msg','solana-program-memory','solana-instruction','solana-account-info']
base=pathlib.Path('/Users/dominic/.cargo/registry')
for p in lock['package']:
 if p['name'] not in names:continue
 stem=p['name']+'-'+p['version'];src=next((base/'src').glob('*/'+stem),None);archive=next((base/'cache').glob('*/'+stem+'.crate'),None)
 row=dict(package=stem,lock_checksum=p.get('checksum'),archive_present=bool(archive),source_present=bool(src),files=[])
 if archive and src:
  row['archive_sha256']=hashlib.sha256(archive.read_bytes()).hexdigest();assert row['archive_sha256']==p['checksum']
  with tarfile.open(archive) as t:
   for f in src.glob('src/*.rs'):
    rel=str(f.relative_to(src));data=f.read_bytes();assert data==t.extractfile(stem+'/'+rel).read()
    matches=[dict(line=i+1,text=l) for i,l in enumerate(data.decode().splitlines()) if re.search(r'target_os|target_arch|BPF_ALIGN|align_offset|pub (unsafe )?fn (hashv|create_program_address|try_find_program_address|set_return_data|get_return_data|invoke|deserialize|get_stack_height)|fn (alloc|dealloc)',l)]
    row['files'].append(dict(path=rel,sha256=hashlib.sha256(data).hexdigest(),matches=matches))
 sdk.append(row)
(E/'NCR_SDK_SCAN.json').write_text(json.dumps(sdk,indent=2)+'\n')
print('samples',len(samples),'lanes',len({s['path'].split('/')[1] for s in samples}),'unresolved commands',[s['path'] for s in samples if not any(x=='kani' or x.endswith('/cargo-kani') or x.endswith('/kani-driver') for x in s['effective_command'])]);print('SDK',[(x['package'],x.get('archive_sha256')==x['lock_checksum']) for x in sdk])
