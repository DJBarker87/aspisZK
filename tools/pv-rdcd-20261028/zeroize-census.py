from pathlib import Path
import json
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');j=json.load(open(D/'zeroize-census-inputs.json'));rt=Path.read_text;rb=Path.read_bytes;wt=Path.write_text
outputs={};root='/pv-rdcd-census/'
def text(p,*a,**k):
 if str(p)==root+j['source_path']:return j['source_text']
 return rt(p,*a,**k)
def data(p,*a,**k):
 if str(p)==root+j['source_path']:return j['source_text'].encode()
 return rb(p,*a,**k)
def write(p,s,*a,**k):
 if str(p).startswith(root):outputs[str(p)]=s;return len(s)
 return wt(p,s,*a,**k)
Path.read_text=text;Path.read_bytes=data;Path.write_text=write
exec(compile(j['script_text'],root+j['script_path'],'exec'),{'__name__':'__main__','__file__':root+j['script_path']})
Path.read_text=rt;Path.read_bytes=rb;Path.write_text=wt
(D/'zeroize-census-result.json').write_text(json.dumps(dict(original_script_sha256=j['script_sha256'],outputs=outputs),indent=2)+'\n')
