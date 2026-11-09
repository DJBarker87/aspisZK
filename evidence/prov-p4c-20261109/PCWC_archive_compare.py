#!/usr/bin/env python3
"""Compare fresh (rebuilt-original-Aeneas) emissions of the archived cut packets with the archived generated Lean."""
import subprocess,hashlib,json,difflib,sys
sys.dont_write_bytecode=True
sha=lambda b:hashlib.sha256(b).hexdigest()
R='docs/research/100bit-spend-path-20261013/evidence/'
def gs(p): return subprocess.check_output(['git','show','research:'+R+p])
items=[('PCWC_E003','AspisR1WithdrawalCaller',{'Funs':open('/tmp/p4c_wc/extraction-a/generated/AspisR1WithdrawalCaller/Funs.lean','rb').read(),'Types':open('/tmp/p4c_wc/extraction-a/generated/AspisR1WithdrawalCaller/Types.lean','rb').read()},'archive caller-extraction-evidence.tar.gz extraction-a/generated'),
 ('PCWC_E004','AspisR1SemanticCallExtraction',{k:gs(f'source-proof-loop-extraction-20261019/AspisR1SemanticCallExtraction.{k}/source.lean') for k in ['Funs','Types']},'source-proof-loop-extraction-20261019/*/source.lean'),
 ('PCWC_E005','AspisR1BatchedWeightsExtraction',{k:gs(f'source-proof-loop-extraction-20261019/AspisR1BatchedWeightsExtraction.{k}/source.lean') for k in ['Funs','Types']},'source-proof-loop-extraction-20261019/*/source.lean')]
out={}
for run,ns,ref,src in items:
    r={}
    for k,a in ref.items():
        f=open(f'{run}_emitted/raw/{ns}/{k}.lean','rb').read()
        d=''.join(difflib.unified_diff(a.decode().splitlines(1),f.decode().splitlines(1),'archived','fresh'))
        r[k]=dict(archived_sha256=sha(a),fresh_sha256=sha(f),identical=a==f,diff=d[:6000],diff_lines=d.count('\n'))
    out[run]=dict(namespace=ns,archived_from=src,files=r)
    print(run,{k:(v['identical'],v['diff_lines']) for k,v in r.items()})
json.dump(out,open('PCWC_ARCHIVE_COMPARE.json','w'),indent=1)
