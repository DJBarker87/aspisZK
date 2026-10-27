"""Check accepted source cuts against raw retained emission; no compilation."""
from pathlib import Path
import re,json,hashlib
r=Path(__file__).resolve().parents[2];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-dict-20261026/resume';p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z';rows=[]
sha=lambda x:hashlib.sha256(x).hexdigest()
def check(name,s,raw,changes):
 q=p/(name+'.lean');assert q.read_text()==s,name
 rows.append(dict(module='R1Z/'+name,source_sha256=sha(q.read_bytes()),raw_sha256=sha(raw.encode()),normalization=changes))
def strip(s):return re.sub(r'(?m)^set_option (maxHeartbeats|maxRecDepth) .*\n','',s)
raw=(e/'sha/Funs.lean.txt').read_text();s=strip(raw).replace('import PDictSHAConsts.Types','import R1Z.PDict_CryptoTypesSource').replace('namespace PDict_SHAConsts','namespace PDict_CryptoTypes').replace('end PDict_SHAConsts','end PDict_CryptoTypes').replace('namespace PDict_CryptoTypes\n','namespace PDict_CryptoTypes\nabbrev digest.InvalidOutputSize := Unit\n',1)
check('PDict_SHAConstructorSource',s,raw,'Only resource options/import/namespace; InvalidOutputSize alias matches raw Types; existing Sha256VarCore fields match raw Types')
assert 'def digest.InvalidOutputSize := Unit' in (e/'sha/Types.lean.txt').read_text()
for text in [(e/'sha/Types.lean.txt').read_text(),(p/'PDict_CryptoTypesSource.lean').read_text()]:
 assert re.search(r'structure sha2.core_api.Sha256VarCore where\n  state : Array Std.U32 8#usize\n  block_len : Std.U64',text)
raw=(e/'path-ref/Funs.lean.txt').read_text();s=strip(raw).replace('import PDictPathRef.Types','import R1Z.PDict_PathTypesSource').replace('PDict_PathRef','PDict_PathTypes')
check('PDict_PathRefSource',s,raw,'Only resource options/import/namespace; existing Path field identical to raw Path type')
raw=(e/'digest-trait/Funs.lean.txt').read_text();a=raw.index('def digest.digest.Digest.Blanket.new\n');b=raw.index('\n/--',a);body=raw[a:b].replace('def digest.digest.Digest.Blanket.new','def digestNew');s='''import R1Z.PDict_Publication
set_option autoImplicit false
namespace R1Z.PDict_DigestNew
open Aeneas Aeneas.Std ProverRwFull
variable [ExternalTypes]
'''+body+'\nend R1Z.PDict_DigestNew\n'
check('PDict_DigestNew',s,raw,'Exact generic method cut, renamed; retained original generic trait interface')
raw=(e/'digest-delegates/Funs.lean.txt').read_text();a=raw.index('def digest.digest.Digest.Blanket.update\n');b=raw.index('\n/--',a);body=raw[a:b].replace('def digest.digest.Digest.Blanket.update','def digestUpdate');assert body in (p/'PDict_DigestDelegates.lean').read_text()
rows.append(dict(module='R1Z/PDict_DigestDelegates',raw_sha256=sha(raw.encode()),source_sha256=sha((p/'PDict_DigestDelegates.lean').read_bytes()),normalization='Update is exact generic method cut; rejected finalize_fixed callback not installed'))
raw=(e/'error-kind/Funs.lean.txt').read_text();a=raw.index('def core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq\n');b=raw.index('\n/--',a);body=raw[a:b].replace('def core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq','def eq').replace('core.io.error.ErrorKind','ProverRwFull.core.io.error.ErrorKind');assert body in (p/'PDict_ErrorKind.lean').read_text()
ret=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullTypes.lean').read_text();ctors=lambda s:re.findall(r'^\| (\w+) : core.io.error.ErrorKind$',s,re.M);assert ctors(ret)==ctors((e/'error-kind/Types.lean.txt').read_text())
rows.append(dict(module='R1Z/PDict_ErrorKind',raw_sha256=sha(raw.encode()),source_sha256=sha((p/'PDict_ErrorKind.lean').read_bytes()),normalization='Exact derived equality body; identical42-constructor enum and existing source discriminants; symbolic injectivity helper'))
for q in p.glob('PDict_*.lean'):
 s=q.read_text();assert not re.search(r'\bsorry\b|\bnative_decide\b|(?m:^axiom\b)',s),q
(e/'source-normalization.json').write_text(json.dumps(rows,indent=2)+'\n');print('checked',len(rows),'source cuts')
