"""Offline identity-only preparation from immutable merged Git blobs."""
import ast
import difflib
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[2]
OUT=ROOT/'evidence/resource-rss-go-v2-20261025'
HERE=Path(__file__).resolve().parent
BASE='f29c3e0e8cb9603b3580706ef15768226fd3fe5c'
OLD='tools/resource-rss-go-20261025/'
RENAMES=[('ResourceRssGO','ResourceRssGOv2'),('resource-rss-go-20261025','resource-rss-go-v2-20261025')]
def pin(b):return dict(sha256=hashlib.sha256(b).hexdigest(),size=len(b))
def main():
    paths=subprocess.check_output(['git','ls-tree','-r','--name-only',BASE,OLD],cwd=ROOT,text=True).splitlines()
    records={}
    for path in paths:
        before=subprocess.check_output(['git','show',BASE+':'+path],cwd=ROOT)
        after=before.decode()
        for old,new in RENAMES:after=after.replace(old,new)
        name=Path(path).name.replace('ResourceRssGO','ResourceRssGOv2')
        target=HERE/name
        with target.open('x') as f:f.write(after)
        normalized=after
        for old,new in reversed(RENAMES):normalized=normalized.replace(new,old)
        assert normalized.encode()==before
        assert ast.dump(ast.parse(normalized),include_attributes=True)==ast.dump(ast.parse(before),include_attributes=True)
        for suffix,content in [('before.py.txt',before),('after.py.txt',after.encode())]:
            with (OUT/(name+'.'+suffix)).open('xb') as f:f.write(content)
        records[name]=dict(base=BASE,path=path,before=pin(before),after=pin(after.encode()),normalized_bytes_equal=True,normalized_ast_equal=True)
    with (OUT/'ResourceRssGOv2-identity-mapping.json').open('x') as f:json.dump(dict(renames=RENAMES,files=records),f,indent=2,sort_keys=True);f.write('\n')
if __name__=='__main__':main()
