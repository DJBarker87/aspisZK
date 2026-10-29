"""Capture both pinned std sources for each standard-library declaration in LLBC."""
from pathlib import Path
import json,subprocess,hashlib,lzma,sys
from run import H
variant=sys.argv[1]
p=H/('PV_B3P_227_'+variant+'_resume5.llbc');x=json.loads(p.read_text())['translated'];files={f['id']:f for f in x['files']};out=dict(llbc_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),variant=variant,declarations=[],files={})
pool={}
def visit(o):
 if isinstance(o,dict):
  if 'HashConsedValue'in o:pool[o['HashConsedValue'][0]]=o['HashConsedValue'][1]
  for v in o.values():visit(v)
 elif isinstance(o,list):
  for v in o:visit(v)
visit(x)
def expand(o):
 if isinstance(o,dict):
  if 'Deduplicated'in o:return expand(pool[o['Deduplicated']])
  if 'HashConsedValue'in o:return expand(o['HashConsedValue'][1])
  return {k:expand(v)for k,v in o.items()}
 if isinstance(o,list):return [expand(v)for v in o]
 return o
for f in x['fun_decls']:
 if not f:continue
 parts=[a['Ident'][0] for a in f['item_meta']['name'] if 'Ident'in a]
 if parts[0] not in ('std','alloc','core'):continue
 span=f['item_meta']['span']['data'];file=files[span['file_id']];path=file['name']['Local'].split('/library/',1)[1]
 row=dict(id=f['def_id'],name='::'.join(parts),full_name=f['item_meta']['name'],span=span,file=path,opacity=f['item_meta']['opacity'],signature=expand(f['signature']))
 out['declarations'].append(row)
 if path in out['files']:continue
 out['files'][path]={}
 for cohort,tc in [('extractor','nightly-2026-06-01'),('deployed','1.94.1')]:
  root=Path(subprocess.check_output(['/home/dombarker/.cargo/bin/rustup','run',tc,'rustc','--print','sysroot'],text=True).strip())/'lib/rustlib/src/rust/library';q=root/path;b=q.read_bytes()
  out['files'][path][cohort]=dict(path=str(q),sha256=hashlib.sha256(b).hexdigest(),text=b.decode())
with lzma.open(H/('std227-'+variant+'-resume5.json.xz'),'wt')as z:json.dump(out,z)
print(json.dumps(dict(declarations=len(out['declarations']),files=len(out['files']))))
