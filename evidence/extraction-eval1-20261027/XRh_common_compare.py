from pathlib import Path
import hashlib,json,difflib
B=Path(__file__).resolve().parent
old=B/'XRh_pinned_generated_01/XRh_Release';new=B/'XRh_new_generated_shared/XRh_Eval'
def h(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
def block(s,needle):
 i=s.index(needle);i=s.rfind('/--',0,i);j=s.find('/--',s.index(needle)+len(needle));return s[i:j if j>=0 else len(s)].rstrip()+'\n'
r=dict(functions={},carriers={},libraries={})
for name in ['verifier.candidate.same_batch_index','verifier.candidate.batch_leaf']:
 o=block((old/'Funs.lean').read_text(),'def '+name);n=block((new/'Funs.lean').read_text(),'def '+name)
 stem=name.rsplit('.',1)[1]
 (B/('XRh_common_'+stem+'.pinned.lean.txt')).write_text(o);(B/('XRh_common_'+stem+'.new.lean.txt')).write_text(n)
 diff=''.join(difflib.unified_diff(o.splitlines(True),n.splitlines(True),fromfile='pinned',tofile='new'))
 (B/('XRh_common_'+stem+'.diff')).write_text(diff)
 r['functions'][name]=dict(pinned_sha256=hashlib.sha256(o.encode()).hexdigest(),new_sha256=hashlib.sha256(n.encode()).hexdigest(),pinned_bytes=len(o.encode()),new_bytes=len(n.encode()),text_identical=o==n,diff=diff)
for label,p in [('pinned',old/'Types.lean'),('new',new/'Types.lean')]:
 s=p.read_text();v=block(s,'structure aspis_core.digest.Digest32');(B/('XRh_common_dictionary.'+label+'.lean.txt')).write_text(v);r['carriers'][label]=dict(file=str(p),sha256=h(p),dictionary=v)
for label,p in [('pinned',Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_toolchain/aeneas/backends/lean/Aeneas/Std/Primitives.lean')),('new',B/'XRh_new_aeneas/backends/lean/Aeneas/Std/Primitives.lean')]:
 s=p.read_text();i=s.index('inductive Error');j=s.index('instance Result_Inhabited',i) if label=='pinned' else s.index('def bind',i)
 text=s[i:j];(B/('XRh_common_effect.'+label+'.lean.txt')).write_text(text);r['libraries'][label]=dict(file=str(p),sha256=h(p),result_definition=text)
(B/'XRh_common_comparison.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({n:{k:v for k,v in d.items() if k!='diff'} for n,d in r['functions'].items()}),flush=True)
