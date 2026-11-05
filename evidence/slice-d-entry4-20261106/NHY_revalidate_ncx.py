"""Read-only revalidation of retained native fragments; no proof replays."""
from pathlib import Path
import hashlib,json,lzma,re,subprocess,sys,time,resource
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1];N=E.parent/'native-decref2-20261028';F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';start=time.monotonic()
sha=lambda b:hashlib.sha256(b).hexdigest()
read=lambda p:json.loads(p.read_text())
def frozen(n):return subprocess.check_output(['git','show',F+':'+n],cwd=R).decode()
def apply(text):
 out={};lines=text.splitlines(keepends=True);i=0
 while i<len(lines):
  if not lines[i].startswith('--- '):i+=1;continue
  old=lines[i][4:].strip();i+=1;assert lines[i].startswith('+++ ');name=lines[i][4:].strip().removeprefix('b/');i+=1
  src=[] if old=='/dev/null' else frozen(name).splitlines(keepends=True);pos=0;dst=[]
  while i<len(lines) and not lines[i].startswith('--- '):
   if lines[i].startswith('@@ '):
    m=re.match(r'@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@',lines[i]);assert m
    at=max(int(m[1])-1,0);dst+=src[pos:at];pos=at;i+=1
    while i<len(lines) and lines[i][:1] in [' ','+','-'] and not lines[i].startswith('--- '):
     line=lines[i];i+=1
     if line[0] in [' ','-']:assert pos<len(src) and src[pos]==line[1:],(name,pos);pos+=1
     if line[0] in [' ','+']:dst.append(line[1:])
   else:i+=1
  dst+=src[pos:];out[name]=''.join(dst)
 return out
rows=[];pins={}
for k in [1,2,4,5,6,7,27,28,29,30]:
 a=f'NCX_K{k:03}';p=N/a/'sources/NCX_harness.patch';files=apply(p.read_text());r=read(N/a/'receipt.json');pins[str(p.relative_to(R))]=sha(p.read_bytes())
 for n,s in files.items():assert sha(s.encode())==r['source_hashes']['NCX_src/'+n],(a,n)
 frozen_path='crates/aspis-statement/src/pool_v1/verifier_registry.rs'
 erased=re.sub(r'^#\[cfg_attr\(kani,.*\]\n','',files[frozen_path],flags=re.M)
 assert erased==frozen(frozen_path),(a,'actual frozen function body drift')
 for n in ['NCX_gate.py','NCX_frozen_graph.sha256']:
  p=N/a/'sources'/n;assert sha(p.read_bytes())==r['source_hashes'][n]
 assert r['source_hashes']['NCX_src/Cargo.lock']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
 assert r['source_hashes']['NCX_KMX_copy_stubs.patch']=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3' and int(r['swaps'])==0
 ad=read(N/(a+'-admission-0.json'));assert ad['exit']==0 and ad['reservation']['allowed'] is True
 lp=N/a/'stdout.log';log=lp.read_text() if lp.exists() else lzma.decompress(lp.with_suffix('.log.xz').read_bytes()).decode();expected=0 if k in [1,4,6,27,29] else 1
 assert r['exit_status']==expected and 'timed out' not in log
 if expected:assert re.search(r'\*\* 1 of \d+ failed',log) and 'Failed Checks:' in log
 else:assert 'VERIFICATION:- SUCCESSFUL' in log
 assert not any(re.search(r'^\s*(?:pub\s+)?static\s',s,re.M) for n,s in files.items() if n.endswith('NCX_native.rs'))
 g=N/(a+'-graph.json');graph=read(g);pins[str(g.relative_to(R))]=sha(g.read_bytes())
 for n in ['NCX_gate.py','NCX_frozen_graph.sha256']:
  pins[str((N/a/'sources'/n).relative_to(R))]=sha((N/a/'sources'/n).read_bytes())
 assert graph['graph_matches_frozen'] and graph['offline'] and graph['lock_unchanged']
 assert graph['lock_before_sha256']==graph['lock_after_sha256']==r['source_hashes']['NCX_src/Cargo.lock']
 assert graph['KMX_patch_sha256']==r['source_hashes']['NCX_KMX_copy_stubs.patch']
 rows.append(dict(attempt=a,exit_status=expected,source_patch_verified=True,no_writable_static=True,receipt_sha256=sha((N/a/'receipt.json').read_bytes()),graph_sha256=sha(g.read_bytes()),source_hashes=r['source_hashes']))
 if k==4:
  native=files['crates/aspis-statement/src/NCX_native.rs'];reference=files['crates/aspis-statement/src/NCX_reference.rs']
  (E/'NHY_NCX_NATIVE_REVIEW.txt').write_text('Functions: '+', '.join(re.findall(r'(?:pub )?fn (\w+)',native))+'\nNative and emitted safe-reference bodies require explicit qualification/status/error carrier review before row admission. Reconstructible patches verified without rerunning passing shapes.\n')
def fn(text,name):
 m=re.search(r'\bfn '+name+r'\b',text);assert m;beg=text.index('{',m.end());i=beg+1;depth=1
 while depth:
  depth+=(text[i]=='{')-(text[i]=='}');i+=1
 return text[beg:i]
body_reviews=[]
for actual,emitted in [('valid_registry_ref','validate_verifier_registry_v2'),('valid_entry_ref','validate_verifier_registry_entry_v2')]:
 a=fn(native,actual);b=fn(reference,emitted)
 # Only namespace qualification is erased; every operator, literal, field,
 # branch and error constructor token must remain identical.
 normalized=a.replace('crate::NCX_reference::','')
 assert re.findall(r'\w+|[^\w\s]',normalized)==re.findall(r'\w+|[^\w\s]',b)
 body_reviews.append(dict(native=actual,reference=emitted,native_body_sha256=sha(a.encode()),reference_body_sha256=sha(b.encode()),normalization='erase crate::NCX_reference:: and lexical whitespace only',exact_tokens=True,domain='Every complete typed record; all 12 FormatError constructors preserved by NCX_Carrier, no success restriction'))
assert sha(reference.encode())==read(N/'NCX_SOURCE_PINS.json')['reference_sha256']
out=dict(status='PASS_NATIVE_REFERENCE_AND_RECONSTRUCTION',rows=rows,pins=pins,body_reviews=body_reviews,whole_root_credit=False,remaining='Decoder roots remain OPEN. Validator-only admission additionally needs coherent NCX_Carrier, NHY_NCXValidators and the raw/headline audit; no passing shape was rerun.',exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),print_axioms='N/A read-only Python reconstruction')
(E/'NHY_NCX_REVALIDATION.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status=out['status'],retained_fragments=len(rows))))
