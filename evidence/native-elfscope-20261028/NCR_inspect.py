import subprocess,json,pathlib,re,hashlib
O=pathlib.Path(__file__).parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def git(*args):return subprocess.check_output(['git',*args])
paths=git('ls-tree','-r','--name-only','HEAD','evidence').decode().splitlines()
lanes=sorted({p.split('/')[1] for p in paths if re.match(r'evidence/(native-|kani-|leaf-p6-)',p)})
samples=[]
for lane in lanes:
 ps=[p for p in paths if p.startswith('evidence/'+lane+'/') and p.endswith('receipt.json') and not 'reservation' in p]
 ps.sort(key=lambda p: (not bool(re.search(r'_K[0-9]',p)),p))
 found=0
 for p in ps:
  try:j=json.loads(git('show','HEAD:'+p))
  except (ValueError,subprocess.CalledProcessError):continue
  cmd=j.get('command',j.get('cmd',[]))
  if not isinstance(cmd,list) or not (j.get('kind')=='kani' or any(str(x)=='kani' or str(x).endswith('/cargo-kani') for x in cmd)):continue
  samples.append(dict(path=p,receipt=j));found+=1
  if found>=2:break
p='evidence/native-u04d-20261028/NCF_K063/receipt.json'
if not any(x['path']==p for x in samples):samples.append(dict(path=p,receipt=json.loads(git('show','HEAD:'+p))))
(O/'NCR_RECEIPT_SAMPLE.json').write_text(json.dumps(samples,indent=2)+'\n')
inv=json.load(open('evidence/native-inv1-20261027/NBI1_INVENTORY.json'))
cache={};hits=[];pins=[]
for f in inv['functions']:
 p=f['file']
 if p not in cache:cache[p]=git('show',rev+':'+p)
 b=cache[p];lo,hi=f['body_byte_range'];assert hashlib.sha256(b[lo:hi]).hexdigest()==f['body_sha256']
 lines=b.decode().splitlines();start=max(0,f['line']-8);end=f['end_line']
 h=[dict(line=i+1,text=lines[i]) for i in range(start,end) if re.search(r'cfg[!(]|#\[cfg|debug_assert|target_os|target_arch|target_pointer|unsafe|align_of|size_of|transmute|read_unaligned',lines[i])]
 if h:hits.append(dict(row=f['row'],file=p,name=f['name'],owner=f['owner'],unit=f['bridge_unit'],start=f['line'],end=end,hits=h))
for p,b in cache.items():pins.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest()))
(O/'NCR_REACHED_SCAN.json').write_text(json.dumps(dict(revision=rev,functions_checked=len(inv['functions']),source_pins=pins,hits=hits),indent=2)+'\n')
for s in samples:
 j=s['receipt'];cmd=j.get('command',j.get('cmd'));print(s['path'],json.dumps(cmd),json.dumps(j.get('env',j.get('environment',{}))))
print('REACHED HITS');print(json.dumps(hits,indent=2))
