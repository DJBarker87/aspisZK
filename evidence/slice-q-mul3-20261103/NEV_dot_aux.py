"""Checked small outside-Q bridges only. Never promotes a slice row."""
from pathlib import Path
import json,hashlib,re,copy,sys
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
from NEV_composition import own_native
from NEV_accum_packet import proof
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pair(a,b,target,flag):
 module='fast_pairing::canonical::NEV_dot_ctor::'+target
 p=own_native(a,0,module);n=own_native(b,1,module)
 assert p['source_hashes']==n['source_hashes'] and p['native_command']==n['native_command']
 pe=copy.deepcopy(p['env']);ne=copy.deepcopy(n['env']);assert ne.pop('RUSTFLAGS')==pe.pop('RUSTFLAGS')+' --cfg '+flag and pe==ne
 for suffix in ['-graph-check.json','-tool-check.json']:assert obj(E/(a+suffix))==obj(E/(b+suffix))
 src=(E/a/'sources/NEV_src/crates/aspis-r1-cost-probe/src/NEV_dot_ctor.rs').read_text()
 assert src.count('fn '+target+'()')==1 and 'cfg!('+flag+')' in src
 assert not re.search(r'\bstatic\s+(?:mut\s+)?\w|Option\s*<\s*fn|stub_verified|proof_for_contract',src)
 return dict(positive=a,negative=b,function=module,flag=flag,status='CHECKED_CUT_ONLY')
def copies(a,b,members):
 p=own_native(a,0,'NEV_copy::KMX_checks::KMX_ptr_correct');n=own_native(b,1,'NEV_copy::KMX_checks::KMX_ptr_wrong')
 assert p['source_hashes']==n['source_hashes'] and p['env']==n['env']
 for suffix in ['-graph-check.json','-tool-check.json']:assert obj(E/(a+suffix))==obj(E/(b+suffix))
 for m in members:
  r=obj(E/m/'receipt.json')
  x=dict(r['source_hashes']);y=dict(p['source_hashes'])
  # Reconstructed payload adds ONLY an extra pin for the same frozen lock.
  # This strengthens the control; every old pin and every Rust byte agrees.
  key='NEV_SOURCE_PINS.json'
  rx=obj(E/m/'sources'/key);py=obj(E/a/'sources'/key)
  lock='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
  assert set(rx)^set(py)<=set(['Cargo.lock'])
  assert rx.get('Cargo.lock',lock)==py.get('Cargo.lock',lock)==lock
  rx['Cargo.lock']=lock;py['Cargo.lock']=lock
  assert rx==py and json.dumps(rx,sort_keys=True)==json.dumps(py,sort_keys=True)
  x.pop(key);y.pop(key);assert x==y
  env=copy.deepcopy(r['env']);env['RUSTFLAGS']=re.sub(r' --cfg NEV_wrong_\w+$','',env['RUSTFLAGS']);assert env==p['env']
  for suffix in ['-graph-check.json','-tool-check.json']:assert obj(E/(a+suffix))==obj(E/(m+suffix))
 return dict(positive=a,negative=b,same_source_members=members)
def run():
 frozen=obj(E/'NEV_FROZEN.json');prefix=frozen['crates/aspis-r1-cost-probe/src/fast_pairing.rs'].split('/// Candidate exact accumulator for sums of `WideExact * WideExact`.')[0]
 for label,namespace in [('NEV_E003','NEV_QRaw'),('NEV_E005','NEV_EbyPushRaw')]:
  pin=obj(E/label/'NEV_EXTRACTION_PINS.json');assert pin['exit']==pin['charon_exit']==0 and pin['lock_before']==pin['lock_after']
  assert pin['pairing_prefix_sha256']==hashlib.sha256(prefix.encode()).hexdigest()
  for name,h in pin['outputs'].items():
   p=E/name
   if name.endswith('_Template.lean'):p=Path(str(p)+'.txt')
   assert sha(p)==h
  for name,h in pin['actual_core_sources'].items():assert h==hashlib.sha256(frozen[name].encode()).hexdigest()
 original=(E/'NEV_extracted/NEV_EbyPushRaw/Types.lean').read_text()
 # Exact structural schema before lossless nominal identification.
 schema={name:re.findall(r'^  (\w+) : ([^\n]+)',body,re.M) for name,body in re.findall(r'structure ([\w.]+) where\n(.*?)(?=\n/--|\nend)',original,re.S)}
 assert schema=={'aspis_core.field.CM31':[('a','aspis_core.field.M31'),('b','aspis_core.field.M31')],'aspis_core.field.QM31':[('c0','aspis_core.field.CM31'),('c1','aspis_core.field.CM31')],'aspis_core.field.wide_exact.WideExact':[('c0','aspis_core.field.QM31'),('c1','aspis_core.field.QM31')],'fast_pairing.canonical.Dot':[('sums','Array Std.U64 4#usize')],'fast_pairing.EbyKDot':[('c0','fast_pairing.canonical.Dot'),('c1','fast_pairing.canonical.Dot'),('count','Std.Usize')]}
 assert (E/'NEV_EbyPushRaw/Funs.lean').read_bytes()==(E/'NEV_extracted/NEV_EbyPushRaw/Funs.lean').read_bytes()
 for label,path in [('NEV_L071','NEV_QRaw/Types'),('NEV_L072','NEV_QRaw/Funs'),('NEV_L080','NEV_EbyPushRaw/Types'),('NEV_L081','NEV_EbyPushRaw/FunsExternal'),('NEV_L082','NEV_EbyPushRaw/Funs')]:
  r=obj(E/label/'receipt.json');assert r['exit_status']==0 and sha(E/(path+'.lean'))==r['source_hashes']['NEV_generated/'+path+'.lean']
 evid=[proof('NEV_L078',['NEV_QRawAssociation.actual','NEV_QRawAssociation.cohort']),proof('NEV_L079',['NEV_DotPush.association','NEV_DotPush.complete']),proof('NEV_L084',['NEV_EbyPushAssociation.source']),proof('NEV_L087',['NEV_EbyDomains.value','NEV_EbyDomains.scalar','NEV_EbyDomains.total'])]
 native=[pair('NEV_K050','NEV_K051','dot_push_iteration','NEV_wrong_dot_iteration'),pair('NEV_K052','NEV_K053','eby_push_context','NEV_wrong_eby_context')]
 control=[copies('NEV_K054','NEV_K055',['NEV_K050','NEV_K051']),copies('NEV_K056','NEV_K057',['NEV_K052','NEV_K053'])]
 return dict(status='CLOSED_CONDITIONAL_AUXILIARY',functions=['canonical::Q::raw','canonical::Dot::push','EbyKDot::push'],domain='Q raw/Dot: canonical private Q operands; arbitrary owned sums. EbyK: canonical WideExact, arbitrary raw QM31 scalar and arbitrary count/sums; failed count or scalar preserves complete receiver. Reached Dot domains derive from SAME from_wide and checked_q outputs.',method='Raw E003 actual extraction; Eby E005 actual extraction with lossless nominal carriers and concrete bindings. Dot retained exact emitted body plus native one iteration and retained finite induction, not failed E002/E004 output. P6/D188 option A reclassification retained.',lean=evid,native=native,copy_controls=control,composed_rows_closed=[])
if __name__=='__main__':
 result=run();(E/'NEV_DOT_AUX.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'])
