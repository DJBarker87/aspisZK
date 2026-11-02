"""Capture Rust source origins for the residual-arm own-1 argument, read only."""
from pathlib import Path
import subprocess,json,hashlib,lzma,re,argparse
R=Path('evidence/pv-b3p6-20261028/resume18');O=R/'std572-source'
a=argparse.ArgumentParser();a.add_argument('--check',action='store_true');args=a.parse_args()
names=['array/mod.rs','ops/control_flow.rs'];versions=['1.94.1','nightly-2026-06-01']
if not args.check:
 code='''from pathlib import Path
import json
out=[]
for v in VERSIONS:
 for name in NAMES:
  p=Path('/home/dombarker/.rustup/toolchains')/(v+'-x86_64-unknown-linux-gnu')/'lib/rustlib/src/rust/library/core/src'/name
  out.append(dict(version=v,name=name,text=p.read_text()))
print(json.dumps(out))
'''.replace('VERSIONS',repr(versions)).replace('NAMES',repr(names))
 rows=json.loads(subprocess.check_output(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True))
 for row in rows:
  p=O/row['version']/(row['name']+'.xz');p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(lzma.compress(row['text'].encode(),preset=6))
sources={(v,n):lzma.decompress((O/v/(n+'.xz')).read_bytes()).decode() for v in versions for n in names}
def body(s,needle):
 start=s.index(needle);i=s.index('{',start);j=i+1;depth=1
 while depth:depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[start:j]
def tokens(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[^\s]',re.sub(r'//[^\n]*|/\*.*?\*/','',s,flags=re.S))
items=[]
for name,needle in [('array/mod.rs','fn try_from_fn_erased'),('ops/control_flow.rs','fn branch(self)'),('ops/control_flow.rs','fn from_residual(residual:')]:
 bs={v:body(sources[(v,name)],needle)for v in versions};same=tokens(bs[versions[0]])==tokens(bs[versions[1]])
 items.append(dict(name=name,needle=needle,bodies=bs,tokens_identical=same));assert same,(name,needle)
x=dict(source_files=[dict(version=v,name=n,sha256=hashlib.sha256(sources[(v,n)].encode()).hexdigest(),path=str(O/v/(n+'.xz')))for v in versions for n in names],items=items,evidence_class='token-identity source parity; compiler-cohort V370 D381/D386 retained',scope='Initializer body and ControlFlow branch/from_residual only. No destructor or pointer parity inferred.')
p=R/'RESIDUAL-SOURCE-PARITY-D572.json';s=json.dumps(x,indent=2)+'\n'
if args.check:assert p.read_text()==s
else:p.write_text(s)
print(json.dumps(dict(items=len(items),all_tokens_identical=True,check=args.check)))
