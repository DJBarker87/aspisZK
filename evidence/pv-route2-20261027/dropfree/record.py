from pathlib import Path
import json,hashlib,re,sys
D=Path(__file__).resolve().parent
meta={
252:dict(batch=2,form='owned Copy Weights; expanded fixed loops',arrays='100 QM31 factors + 30 QM31 points + 2 QM31 extra = 2112 payload bytes, plus Variant/padding; removes one Box allocation',caller='YES: replace Box storage, signatures and return handling; all consumers must accept the owned carrier',quantifier='all shipped Variant/alpha/z values; Result error tags kept; allocation/failure/timing equivalence unproved'),
249:dict(batch=2,form='fixed arrays, scalar little-endian decode, public canonical-limb decoder',arrays='two [u32;8] arrays (64 bytes) plus 32-byte WideExact result; same payload arrays as shipped, no heap allocation in shipped sampler',caller='NO signature change; redirect plus field/source bridge',quantifier='all 32-byte blocks; no digest specialization'),
250:dict(batch=2,form='fixed arrays, scalar little-endian decode, public canonical-limb decoder',arrays='two [u32;8] arrays (64 bytes) plus 32-byte WideExact result; same payload arrays as shipped',caller='NO signature change; redirect plus field/source bridge',quantifier='all 32-byte blocks'),
226:dict(batch=3,form='fixed public projection, [u8;1455] plus returned length',arrays='1455-byte result buffer; 1455 transfer / 1427 withdrawal used bytes; owned input projection also copies fixed public data',caller='YES: flatten Public and consume only output[..len]; return carrier and caller storage change',quantifier='both shipped Public variants via explicit projection; Error::Public preserved, native allocation effects unproved'),
134:dict(batch=3,form='constant endpoint table; counted validation and direct membership masks',arrays='136 pairs of u16 = 544 static bytes; 2 x [u8;1024] counters = 2048 scratch bytes; [u16;64] output = 128 bytes; removes temporary schedule/active-row Vecs',caller='NO result-shape change except source error-carrier binding; redirect requires table/source transport, not a caller algorithm rewrite',quantifier='no arguments as shipped; fixed schedule only; explicit endpoint errors retained; Shape unreachable at fixed size'),
36:dict(batch=3,form='Copy T, generic const N/CAP, owned fixed-capacity Buffer; complete Err carrier retained',arrays='CAP*sizeof(T)+usize input carrier; N*sizeof(T) output; removes Vec allocation only under changed representation',caller='YES: caller buffer ownership and length invariant plus Copy bound and fill value; generic non-Copy/Drop Vec row NOT covered',quantifier='NARROWED: T:Copy and len<=CAP representation; arbitrary destructible T/Vec quantifier retained as open')}
for op in [205,212,215,216,217,219]:meta[op]=dict(batch=3,form='concrete owned SHA-256 state/buffer and index-based compression/padding',arrays='[u32;8] state 32B + u64 block count + [u8;64] buffer + usize position = 112B on 64-bit target; [u32;64] schedule 256B scratch + [u8;32] output',caller='YES: concrete state, fixed byte output and buffering APIs replace generic digest/GenericArray interface',quantifier='NARROWED to concrete SHA-256 with pos<64 and state/buffer representation; generic digest row remains open')
op=int(sys.argv[1]);key=sys.argv[2];src=D/'probes'/f'{op}.rs';m=meta[op];m.update(op=op,key=key,source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),source_lines=len(src.read_text().splitlines()),source_bytes=src.stat().st_size)
O=next((p for p in sorted(D.glob(f'aeneas-{key}*')) if (p/'time.log').exists()),D/f'aeneas-{key}');receipt=O/'receipt.json'
if receipt.exists():
 r=json.loads(receipt.read_text());m['extractor']=r;m['extraction_status']='accepted' if r['exit']==0 else 'refused';m['error']=(O/'output.log').read_text() if r['exit'] else None
else:m['extraction_status']='admission hold'
checks=[]
for p in (D/'lean-receipts').glob('*/receipt.json') if (D/'lean-receipts').exists() else []:
 r=json.loads(p.read_text())
 if r['module'].startswith('PV_R2_DF_'+key.replace('-','_')+'_'):checks.append(r)
m['lean_checks']=checks;m['backend_status']='passed' if len(checks)>=2 and all(r['exit']==0 for r in checks) else 'no accepted emission check yet'
(D/f'op{op}.json').write_text(json.dumps(m,indent=2)+'\n')
