"""Read-only immutable emission replay and source review; no extraction or Kani."""
from pathlib import Path
from types import SimpleNamespace
import json,lzma,re,hashlib,subprocess
E=Path(__file__).resolve().parent;R=Path.cwd();F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';inputs={}
H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 p=Path(p)
 if p.exists():b=p.read_bytes()
 elif Path(str(p)+'.xz').exists():
  b=lzma.decompress(Path(str(p)+'.xz').read_bytes());assert H(b)==Path(str(p)+'.sha256').read_text().strip()
 else:
  r=subprocess.run(['git','show','HEAD:'+str(p)],capture_output=True)
  if r.returncode==0:b=r.stdout
  else:
   b=lzma.decompress(subprocess.check_output(['git','show','HEAD:'+str(p)+'.xz']));assert H(b)==subprocess.check_output(['git','show','HEAD:'+str(p)+'.sha256'],text=True).strip()
 inputs[str(p)]=H(b);return b
def J(p):return json.loads(raw(p))
def put(n,x):(E/('NNM_'+n+'.json')).write_text(json.dumps(x,indent=1)+'\n')
lock=H(subprocess.check_output(['git','show',F+':Cargo.lock']));em=[];syntax=[]
base=Path('evidence/tx1-owned-20261111/NMT_extracted/stage1_owned');p=J(base/'NMT_PINS.json');rc=J('evidence/tx1-owned-20261111/NMT_E003/receipt.json')
assert p['exit']==p['charon_exit']==p['aeneas_exit']==rc['exit_status']==0
assert p['frozen_revision']==F and p['lock_before']==p['lock_after']==lock
assert p['root']=='crate::r1_pool_adapter::owned::stage1_owned' and p['root_features']=='pool-adapter,private-leaf-salts'
for name,h in p['outputs'].items():assert H(raw(base/name))==h
assert H(raw(base/'stage1_owned.llbc'))==p['llbc_sha256']
bc=J('evidence/tx1-owned-20261111/NMT_BC_AUDIT.json');spans=[]
for z in bc['definitions']:
 if z['function']!='stage1_owned':continue
 if 'lines'in z:
  src=subprocess.check_output(['git','show',F+':'+z['file']]);assert H(src)==z['source_sha256'];seg='\n'.join(src.decode().splitlines()[z['lines'][0]-1:z['lines'][1]]);assert H(seg.encode())==z['span_sha256'];assert not re.search(r'\bwhile\b|\bloop\s*\{|\bfor\s+\w+\s+in\b',re.sub(r'//[^\n]*|/\*[\s\S]*?\*/','',seg))
 spans.append(z)
program=raw('evidence/tx1-owned-20261111/NMT_parameterize.py').decode()
class VFile:
 def __init__(self,n):self.n=n
 def read_text(self):return raw(base/'raw/NMT_stage1_owned'/self.n).decode()
class VRoot:
 def __truediv__(self,n):return VFile(n)
ns=dict(raw=VRoot(),a=SimpleNamespace(function='stage1_owned'),re=re)
exec(compile(program[program.index('extern='):program.index("(dest/'Funs.lean').write_text")],'NNM immutable stage1 syntax replay','exec'),ns)
compiled=raw('evidence/tx1-owned-20261111/NMT_lean/NMT_stage1_owned/Funs.lean');assert compiled==ns['funs'].encode()
em.append(dict(row='TX1:345',attempt='NMT_E003',pins=p,receipt={k:rc[k]for k in ['exit_status','wall_seconds','peak_rss_kib','swaps']},bc=spans))
syntax.append(dict(row='TX1:345',status='PASS exact bytes',parameterized_sha256=H(compiled),generator_sha256=H(program.encode()),source_chain=['AspisR1.NMT_345.source_fold','AspisR1.NNG_Tree345.source','AspisR1.NNG_ParentAssociation345.source','AspisR1.NNG_TotalProducer345.interpretation','AspisR1.NNG_TotalProducer345.native'],only_credited_root='AspisR1.NNG_ActualCandidate345.candidate',provisional_candidate_credited=False))
base=Path('evidence/tx2-owned-20261111/NMS_extract_stage2');p=J(base/'NMS_PINS.json');rc=J('evidence/tx2-owned-20261111/NMS_E003/receipt.json')
assert p['exit']==p['charon_exit']==p['aeneas_exit']==rc['exit_status']==0 and p['frozen_revision']==F and p['lock_before']==p['lock_after']==lock
for name,h in p['outputs'].items():assert H(raw(base/name))==h
assert H(raw(base/'stage2.llbc'))==p['llbc_sha256']
funs=raw(base/'raw/NMS_stage2/Funs.lean').decode();owned='programs/r1-cost-probe/src/r1_pool_adapter_owned.rs';src=subprocess.check_output(['git','show',F+':'+owned]);audit=J('evidence/tx2-owned-20261111/NMS_BC_AUDIT.json');assert H(src)==audit['frozen_file_sha256'];assert H(funs.encode())==audit['raw_funs_sha256']
for name,lines in [('validate_asq8',(338,373)),('stage2_owned',(417,445))]:
 assert 'def r1_pool_adapter.owned.'+name+'\n' in funs
 segment='\n'.join(src.decode().splitlines()[lines[0]-1:lines[1]]);assert not re.search(r'\bwhile\b|\bloop\s*\{|\bfor\s+\w+\s+in\b',re.sub(r'//[^\n]*','',segment))
 em.append(dict(row='TX2:242'if name=='validate_asq8'else'TX2:241',attempt='NMS_E003',pins_file=str(base/'NMS_PINS.json'),pins_sha256=H(raw(base/'NMS_PINS.json')),llbc_sha256=p['llbc_sha256'],funs_sha256=H(funs.encode()),exact_definition='NMS_stage2.r1_pool_adapter.owned.'+name,source_lines=lines,source_sha256=H(src),segment_sha256=H(segment.encode()),status='PASS',note='E003 start-from stage2 emits both bodies; E002 validate-only failed before Aeneas and is not used'))
program=raw('evidence/tx2-owned-20261111/NMS_normalize.py').decode()
# Run the original transformation in memory; every write must equal committed bytes.
class Sink:
 def __init__(self,p):self.p=Path(p)
 def __truediv__(self,n):return Sink(self.p/n)
 def read_text(self):return raw(self.p).decode()
 def write_text(self,s):
  if self.p.suffix=='.lean':assert raw(self.p)==s.encode(),str(self.p)
  return len(s)
ns=dict(__file__='evidence/tx2-owned-20261111/NMS_normalize.py')
# Replace only E construction; all original body-normalization logic is executed.
prog=program.replace('E=Path(__file__).resolve().parent',"E=Sink('evidence/tx2-owned-20261111')")
ns['Sink']=Sink;exec(compile(prog,'NNM immutable NMS replay','exec'),ns)
syntax.append(dict(rows=['TX2:242','TX2:241'],status='PASS exact normalized bytes',generator_sha256=H(program.encode()),association='NMS_Emitted.validate and stage2 separately regenerated from exact E003 definitions',external_bindings=J('evidence/tx2-owned-20261111/NMS_NORMALIZATION.json')['external_bindings']))
# E008 Box wrappers: original parameterization executed read-only, writing report captured.
program=raw('evidence/tx2-auth-20261111/NMX_R4_box_parameterize.py').decode();prog=program.replace('E=Path(__file__).resolve().parent',"E=Sink('evidence/tx2-auth-20261111')")
class BoxSink(Sink):
 @property
 def name(self):return self.p.name
 def __truediv__(self,n):return BoxSink(self.p/n)
 def read_bytes(self):return raw(self.p)
 def relative_to(self,other):return self.p.relative_to(other.p)
ns=dict(Sink=BoxSink);exec(compile(prog,'NNM immutable Box syntax replay','exec'),ns)
base=Path('evidence/tx2-auth-20261111/NMX_auth_box_emitted');p=J(base/'NMX_PINS.json');assert p['exit']==p['charon_exit']==p['aeneas_exit']==0 and p['lock_before']==p['lock_after']==lock
for n,h in p['outputs'].items():assert H(raw(base/n))==h
em.append(dict(row='TX2:233',attempt='NMX_E008',pins=p,receipt_status=J('evidence/tx2-auth-20261111/NMX_E008/receipt.json')['exit_status'],status='PASS',source_audit=J('evidence/tx2-auth-20261111/NMX_R4_SOURCE_AUDIT.json')))
syntax.append(dict(row='TX2:233',status='PASS exact Box wrapper bytes',generator_sha256=H(program.encode()),same_byte_children=['NMX_R4_BoxBinding.master','NMX_R4_BoxBinding.checkpoint'],all_args='NMX_R4_ProjectionRef.reference',observation='NMX_R4_Authentication.observed'))
put('EMISSION_REVIEW',dict(status='PASS',emissions=em,new_extraction=0,trust='(bm)/(bc) increased reliance on existing narrowed extraction item; reclassification, never removal'))
put('SYNTAX_ASSOCIATION',dict(status='PASS',syntax=syntax))
put('REVIEW_INPUTS',inputs)
print('NNM immutable source/emission review PASS; combined gate pending')
