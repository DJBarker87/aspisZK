"""Reconstructible scratch overlay against the frozen release; never applied here."""
from pathlib import Path
import subprocess,json,difflib,hashlib,time,resource,sys
E=Path(__file__).resolve().parent;R=E.parents[1];F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';start=time.monotonic();x=json.loads((E/'NIJ_NATIVE_INPUTS.json').read_text());parts=[];rows=[]
for n,text in sorted(x.items()):
 p=subprocess.run(['git','show',F+':'+n],cwd=R,capture_output=True,text=True);old=p.stdout if p.returncode==0 else ''
 diff=''.join(difflib.unified_diff(old.splitlines(True),text.splitlines(True),fromfile='a/'+n if p.returncode==0 else '/dev/null',tofile='b/'+n))
 parts.append(diff);rows.append(dict(path=n,frozen_sha256=hashlib.sha256(old.encode()).hexdigest() if p.returncode==0 else None,scratch_sha256=hashlib.sha256(text.encode()).hexdigest(),changed=old!=text))
patch=''.join(parts);p=E/'NIJ_HARNESS.patch';p.write_text(patch)
(E/'NIJ_PATCH_MANIFEST.json').write_text(json.dumps(dict(frozen_revision=F,patch=p.name,sha256=hashlib.sha256(patch.encode()).hexdigest(),files=rows,scope='Scratch outside repository only; cfg erasure byte-equal to frozen release. Canonical text overlays and content-addressed proof inputs are receipt/generator inputs, never shipped Rust modules.',KMX_patch='evidence/kani-mitig-20261028/KMX_copy_stubs.patch',KMX_sha256='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67',KMX_applied_separately=True,exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss//(1024 if sys.platform=='darwin' else 1),swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),print_axioms='N/A patch/source validation'),indent=1)+'\n');print('patch files',len(rows),'bytes',len(patch.encode()))
