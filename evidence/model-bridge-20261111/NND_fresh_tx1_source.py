from pathlib import Path
import subprocess,json,re,hashlib,difflib
E=Path(__file__).resolve().parent
rev=json.loads((E/'NND_ZERO_REUSE.json').read_text())['revision']
root='evidence/tx1-owned-20261111/NMT_extracted/tx1/'
raw=subprocess.check_output(['git','show',rev+':'+root+'raw/NMT_tx1/Funs.lean']).decode()
for rel in ['raw/NMT_tx1/Funs.lean','NMT_PINS.json','NMT_DECLARATIONS.json']:
 b=subprocess.check_output(['git','show',rev+':'+root+rel]);p=E/'NND_reuse/NMT_fresh/NMT_extracted/tx1'/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
pins=json.loads((E/'NND_reuse/NMT_fresh/NMT_extracted/tx1/NMT_PINS.json').read_text());assert pins['aeneas_exit']==0 and pins['frozen_revision']=='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
oldpath='docs/research/100bit-spend-path-20261013/lean-candidates/s126-caller-boundary-20261021/CurrentCompactCallerModelV1.lean'
old=subprocess.check_output(['git','show','HEAD:'+oldpath]).decode()
name='verifier.candidate.tx1'
def decl(s):
 s=s[s.index('def '+name):];return s[:s.rfind('\nend ')].strip()
body=decl(raw).replace('def '+name,'def fresh (ops : Ops)',1)
map={'verifier.candidate.parse_shape':'ops.op3','verifier.candidate.canonical_scan':'ops.op4','verifier.candidate.batch_merkle':'ops.op6','verifier.candidate.query_loop':'ops.op7','verifier.checkpoint':'ops.op16','verifier.BatchedWeights.finish':'ops.op17','verifier.BatchedWeights.new':'ops.op18','verifier.QueryGeometry.for_range':'ops.op19','verifier.Accumulator.new':'ops.op20','verifier.candidate.prepare':'(verifier.candidate.prepare ops)','aspis_core.field.wide_exact.WideExact.ZERO':'(aspis_core.field.wide_exact.WideExact.ZERO ops)','compact.OFF_FOLDED_ROOT':'(compact.OFF_FOLDED_ROOT ops)','compact.OFF_ROUND1':'(compact.OFF_ROUND1 ops)'}
changes=[]
for a,b in sorted(map.items(),key=lambda x:-len(x[0])):
 body,n=re.subn(r'(?<![\w.])'+re.escape(a)+r'(?![\w.])',b,body)
 if n:changes.append(dict(symbol=a,replacement=b,count=n))
canonical=decl(old).replace('def '+name,'def fresh',1)
tokens=lambda s:re.findall(r'\w+|[^\s\w]',s)
report=dict(raw_revision=rev,raw_sha256=hashlib.sha256(raw.encode()).hexdigest(),historical_file=oldpath,historical_sha256=hashlib.sha256(old.encode()).hexdigest(),changes=changes,token_equal=tokens(body)==tokens(canonical),qualification='canonical type-owner replay; original nominal conversions and closed child/RSL installations remain separate')
if not report['token_equal']:
 report['diff']='\n'.join(difflib.unified_diff(tokens(canonical),tokens(body)))[:16000]
 (E/'NND_FreshTx1Source.pending').write_text(body)
else:
 header='''import NND_064ParseTransport
set_option autoImplicit false
noncomputable section
namespace NND_FreshTx1Source
open Aeneas Aeneas.Std Result ControlFlow Error AspisR1CurrentCaller
'''
 footer='''
/-- Fresh frozen094 parent source on coherent canonical carriers. All opaque
children stay at the SAME calls; their RSL/domain installation is separate. -/
theorem source (ops : Ops) {H : Type} (D : aspis_core.digest.Digest32 H)
 (p : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (pub proof : Slice U8) (k : Usize) (hash : H)
 (obs : Option (verifier.Phase → Result Unit)) :
 fresh ops D p pub proof k hash obs = verifier.candidate.tx1 ops D p pub proof k hash obs := rfl
#print axioms source
end NND_FreshTx1Source
end
'''
 (E/'NND_FreshTx1Source.lean').write_text(header+canonical+'\n'+footer)
(E/'NND_TX1_SOURCE_REPLAY.json').write_text(json.dumps(report,indent=1)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['diff','changes']}))
