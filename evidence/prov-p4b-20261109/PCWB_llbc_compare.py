#!/usr/bin/env python3
"""Compare a fresh PCWB LLBC (repro.llbc.xz) with the LLBC retained in the archive packet that produced a live module,
and compare the archive's generated Lean with the live module. Output PCWB_LLBC_COMPARE.json. Local, read-only."""
import json,lzma,re,io,tarfile,hashlib,subprocess,sys
from pathlib import Path
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R='/Users/dominic/ZK'
sha=lambda b:hashlib.sha256(b).hexdigest()
def git(p):return subprocess.check_output(['git','-C',R,'show','research:'+p])
EV='docs/research/100bit-spend-path-20261013/'
JOBS=[
 dict(run='PCWB_E008',archive=EV+'evidence/withdrawal-caller-extraction-20261016/caller-extraction-evidence.tar.gz',llbc='extraction-a/WithdrawalCaller.llbc',
      generated={'extraction-a/generated/AspisR1WithdrawalCaller/Funs.lean':EV+'lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Funs.lean','extraction-a/generated/AspisR1WithdrawalCaller/Types.lean':EV+'lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Types.lean'}),
 dict(run='PCWB_E009',archive=EV+'evidence/source-proof-loop-extraction-20261019/semantic-calls-root-v5-results-20261019.tar.gz',llbc='SemanticCalls.llbc',
      generated={'generated/AspisR1SemanticCallExtraction/Funs.lean':EV+'evidence/source-proof-loop-extraction-20261019/AspisR1SemanticCallExtraction.Funs/source.lean','generated/AspisR1SemanticCallExtraction/Types.lean':EV+'evidence/source-proof-loop-extraction-20261019/AspisR1SemanticCallExtraction.Types/source.lean'}),
 dict(run='PCWB_E010',archive=EV+'evidence/source-proof-loop-extraction-20261019/batched-calls-root-v5-results-20261019.tar.gz',llbc='BatchedWeights.llbc',
      generated={'generated/AspisR1BatchedWeightsExtraction/Types.lean':EV+'evidence/source-proof-loop-extraction-20261019/AspisR1BatchedWeightsExtraction.Types/source.lean','generated/AspisR1BatchedWeightsExtraction/Funs.lean':EV+'evidence/source-proof-loop-extraction-20261019/AspisR1BatchedWeightsExtraction.Funs/source.lean'}),
]
def norm(o):
    if isinstance(o,dict):return {k:norm(v) for k,v in o.items()}
    if isinstance(o,list):return [norm(x) for x in o]
    if isinstance(o,str):return re.sub(r'/home/dombarker/project-offloads/[^"]*?(?=/(?:crate|input|src)|$)','<P>',o)
    return o
out=[]
for j in JOBS:
    t=tarfile.open(fileobj=io.BytesIO(git(j['archive'])));names={(n[2:] if n.startswith('./') else n):n for n in t.getnames()}
    old=json.loads(t.extractfile(names[j['llbc']]).read());mine=json.loads(lzma.decompress((E/(j['run']+'_emitted/repro.llbc.xz')).read_bytes()))
    res={}
    for k in mine['translated']:
        a=json.dumps(norm(mine['translated'][k]),sort_keys=True);b=json.dumps(norm(old['translated'][k]),sort_keys=True)
        if a==b:res[k]='equal'
        else:
            A=sorted(json.dumps(x,sort_keys=True) for x in norm(mine['translated'][k]));B=sorted(json.dumps(x,sort_keys=True) for x in norm(old['translated'][k]))
            res[k]='equal_up_to_list_order' if A==B else 'DIFFERENT'
    gen={}
    for member,livepath in j['generated'].items():
        try:a=t.extractfile(names[member]).read()
        except KeyError:gen[member]=dict(note='member absent');continue
        l=git(livepath);gen[member]=dict(archive_sha256=sha(a),live_path=livepath,live_sha256=sha(l),byte_identical=a==l)
    emb=[x for x in old['translated']['files'] if x.get('contents')]
    out.append(dict(run=j['run'],archive=j['archive'],archive_blob_sha256=sha(git(j['archive'])),archived_llbc=j['llbc'],charon_version_fresh=mine['charon_version'],charon_version_archive=old['charon_version'],
      llbc_fields=res,embedded_sources=[dict(name=x['name'],sha256=sha(x['contents'].encode())) for x in emb],generated_vs_live=gen))
(E/'PCWB_LLBC_COMPARE.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps([{k:v for k,v in o.items() if k in('run','llbc_fields')} for o in out]))
