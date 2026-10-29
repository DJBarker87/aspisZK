"""Copy committed NEC evidence, run its strict validator unchanged, pin provenance."""
from pathlib import Path
import subprocess,json,hashlib,re,lzma,importlib.util,tempfile
E=Path(__file__).resolve().parent;B='evidence/slice-s-leaves-20261029/';REV='8cdc45079a';D=E/'NED_imports'/'after';D.mkdir(parents=True,exist_ok=True);used={}
def get(p):
 data=subprocess.check_output(['git','show',REV+':'+p],stderr=subprocess.DEVNULL)
 used[p]=dict(revision=REV,sha256=hashlib.sha256(data).hexdigest());return data
def copy(name,to=None):
 try:data=get(B+name)
 except subprocess.CalledProcessError:data=lzma.decompress(get(B+name+'.xz'))
 p=(D/name if to is None else to);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data);return data
claim=json.loads(copy('NEC_CLOSED.json'))[-1];assert claim['function'].endswith('::decode_pair_afterstate_boxed_v1') and claim['status']=='CLOSED-CONDITIONAL'
modules=['NEC_Reference/Types','NEC_Reference/Funs','NEC_ReplyRef/Types','NEC_ReplyRef/Funs','NEC_AfterstateBox','NEC_AfterstateWindows','NEC_PureReplyAssociation','NEC_StaticReplyTransport']
for m in modules:copy(m+'.lean',E/'NED_imports'/(m+'.lean'))
copy('NEC_validate_packet.py');audit=json.loads(copy('NEC_AFTER_PACKET_AUDIT.json'));feature=json.loads(copy('NEC_FEATURE_REVALIDATION.json'));copy(feature['checked_context'])
pairs=[]
for pair in audit['pairs']:
 a,b=[row['attempt'] for row in pair]
 for attempt in [a,b]:
  for suffix in ['/receipt.json','/stdout.log','/NEC_harness.patch','-lock-check.json','-graph-check.json']:
   copy(attempt+suffix)
  try:copy(attempt+'-actual-graph-check.json')
  except subprocess.CalledProcessError:pass
 neg=(D/b/'stdout.log').read_text();marker=re.search(r'Failed Checks: ([^\n]+)',neg)[1];pairs.append((a,b,marker))
spec=importlib.util.spec_from_file_location('NED_imported_packet_validator',D/'NEC_validate_packet.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
checked=[module.native_pair(*p) for p in pairs]
def body(text):
 a=text.index('fn decode_pair_afterstate_boxed_v1(');i=text.index('{',a);depth=0
 for j in range(i,len(text)):
  if text[j]=='{':depth+=1
  if text[j]=='}':
   depth-=1
   if depth==0:return text[a:j+1]
 raise AssertionError('function not terminated')
frozen_name='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'
frozen_body=body(subprocess.check_output(['git','show','4bb3b3f5:'+frozen_name],text=True))
for pair in pairs:
 for a in pair[:2]:
  patch=(D/a/'NEC_harness.patch').read_bytes()
  with tempfile.TemporaryDirectory(prefix='NED-after-source-') as tmp:
   root=Path(tmp)
   for name in re.findall(r'^--- a/(.+)$',patch.decode(),re.M):
    q=root/name;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(subprocess.check_output(['git','show','4bb3b3f5:'+name]))
   subprocess.run(['git','apply','--unsafe-paths','-'],input=patch,cwd=root,check=True,capture_output=True)
   assert body((root/frozen_name).read_text())==frozen_body,(a,'actual frozen helper body mismatch')

for n in [2,3,4,6,19,20,24,35]:
 for f in ['receipt.json','stdout.log','time.log']:copy(f'NEC_L{n:03d}/'+f)
# No source-to-ELF or allocator qualification is removed by this import.
report=dict(status='CLOSED-CONDITIONAL imported and native receipt/source/feature audit revalidated; composition OPEN',revision=REV,claim=claim,modules=modules,pairs=checked,artifacts=used,frozen_helper_body_sha256=hashlib.sha256(frozen_body.encode()).hexdigest(),new_kani_runs=0,remaining=['DigestDecodeAll child law','callee same-input/domain and physical context at actual late caller','allocator/runtime/ABI and source-to-ELF qualifications retained'])
(E/'NED_AFTER_REVALIDATION.json').write_text(json.dumps(report,indent=1)+'\n');print('Revalidated',len(checked),'NEC pairs; copied',len(modules),'Lean modules')
