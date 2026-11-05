"""Source/body continuity and receipt validation. No compiler/solver launch."""
from pathlib import Path
import json,hashlib,re,subprocess,lzma
E=Path(__file__).resolve().parent;R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def function(s,n):
 m=re.search(r'\bpub fn '+re.escape(n)+r'\s*\(',s);assert m,n
 start=m.start();a=s.index('{',m.end());depth=1;i=a+1
 while depth:
  depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[start:i]
frozen=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:crates/aspis-r1-cost-probe/src/transcript.rs'],text=True)
kit=(E/'NGT_REUSED_TRANSCRIPT_lib.rs.txt').read_text();continuity={}
for n in ['absorb','block','scalar','scalar_k']:
 a=function(frozen,n);b=function(kit,n);assert a==b,n
 continuity[n]=dict(byte_identical=True,frozen_sha256=sha(a.encode()),kit_sha256=sha(b.encode()))
# Native scratch overlays are source-fission modules plus cfg-only appendages.
over=json.loads((E/'NGT_OVERLAY.json').read_text());originals=json.loads((E/'NGT_FROZEN_FILE_PINS.json').read_text());source_errors=[]
for name,h in originals.items():
 p=R/name
 if not p.is_file() or sha(p.read_bytes())!=h:source_errors.append(name)
assert not source_errors,source_errors
for name in ['transcript.rs','sampler.rs']:
 rel='crates/aspis-r1-cost-probe/src/'+name;raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+rel]);actual=(E/over[rel]).read_bytes();assert actual.startswith(raw) and '#[cfg(kani)]' in actual[len(raw):].decode()
rel='crates/aspis-r1-cost-probe/src/lib.rs';raw=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+rel]);assert (E/over[rel]).read_bytes()==b'#![cfg_attr(kani,feature(allocator_api))]\n'+raw
kmx=E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch';assert sha(kmx.read_bytes())=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
for p in [E/'NGT_native.rs.txt',E/'NGT_sampler.rs.txt']:
 s=p.read_text();assert not re.search(r'\bstatic\s+(mut\s+)?\w+\s*:',s);assert 'proof_for_contract' not in s and 'stub_verified' not in s;assert 'Option<fn' not in s
reuse={}
for folder,attempts in [('slice-d-prepare-20261104',['NFW_K013','NFW_K014','NFW_K015','NFW_K016']),('slice-d-checkpoint-20261104',['NGC_K082','NGC_K083','NGC_K084','NGC_K085'])]:
 for a in attempts:
  d=E.parent/folder;p=d/a/'receipt.json';x=json.loads(p.read_text());expected=1 if int(a[-3:])%2==1 and a.startswith('NGC') or int(a[-3:])%2==0 and a.startswith('NFW') else 0
  assert x['exit_status']==expected,(a,x['exit_status']);s=(d/a/'stdout.log').read_text();assert ('VERIFICATION:- FAILED' if expected else 'VERIFICATION:- SUCCESSFUL') in s
  # These sources contain local records, exact KMX stubs and no mutable static.
  srcs=list((d/a/'sources').rglob('*.rs'));relevant=[p for p in srcs if p.name in ['NFW_transcript.rs','NGC_digest.rs']];assert relevant
  for q in relevant:
   t=q.read_text();assert not re.search(r'\bstatic\s+(mut\s+)?\w+\s*:',t);assert 'KMX_copy_nonoverlapping' in t
  g=json.loads((d/(a+'-graph-check.json')).read_text());assert g['graph_matches_frozen'];l=json.loads((d/(a+'-lock-check.json')).read_text());assert l['unchanged']
  reuse[str(p.relative_to(R))]=dict(sha256=sha(p.read_bytes()),source_hashes={str(q.relative_to(R)):sha(q.read_bytes()) for q in relevant},exit=x['exit_status'],graph_sha256=sha((d/(a+'-graph-check.json')).read_bytes()),lock_sha256=sha((d/(a+'-lock-check.json')).read_bytes()))
(E/'NGT_SOURCE_FIDELITY.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',frozen_files=len(originals),source_errors=source_errors,unchanged_method_continuity=continuity,reused_emission='NGT_REUSED_TRANSCRIPT_Funs.lean.txt',reused_emission_sha256=sha((E/'NGT_REUSED_TRANSCRIPT_Funs.lean.txt').read_bytes()),fresh_extraction='NGT_E001: manifest-load failure; not credited',KMX_patch_sha256=sha(kmx.read_bytes()),reused_native=reuse,elf_rebuild_trigger=False),indent=1))
print(json.dumps(dict(source_files=len(originals),methods=len(continuity),reused_native=len(reuse))))
