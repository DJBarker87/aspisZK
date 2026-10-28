"""Check small codec/generator bodies and pin the D371 field-origin review.
This is source association, not a whole-route trace refinement.
"""
from pathlib import Path
import hashlib, json, re, subprocess
R=Path(__file__).resolve().parents[2]
E=R/'evidence/pv-l2c-20261028/resume-d371'
def sha(s): return hashlib.sha256(s.encode()).hexdigest()
def compact(s): return re.sub(r'\s+','',s)
def body(text, marker):
    start=text.index(marker); left=text.index('{',start); depth=1; end=left+1
    while depth:
        depth+=(text[end]=='{')-(text[end]=='}'); end+=1
    return text[left+1:end-1]
core=(R/'crates/aspis-core/src/field.rs').read_text()
scalar=body(core,'pub fn from_le_bytes(bytes: [u8; 4])')
assert compact(scalar)==compact('let v = u32::from_le_bytes(bytes); if v >= P { None } else { Some(M31(v)) }')
statement=(R/'crates/aspis-statement/src/atomic_statement.rs').read_text()
digest=body(statement,'pub fn decode_digest_canonical(')
limbs=[]
for i in range(8):
    indices=', '.join('bytes['+str(4*i+j)+']' for j in range(4))
    limbs.append('M31::from_le_bytes(['+indices+']).ok_or(AtomicStatementError::NonCanonicalDigest)?')
assert compact(digest)==compact('Ok(['+','.join(limbs)+',])')
plan=(R/'tools/r1-cost-probe/src/bin/devnet_spend/plan.rs').read_text()
probe=(R/'tools/pv-l2c-20261028/decoder-probe/main.rs').read_text()
gen=body(plan,'fn digest(')
assert compact(gen)==compact(body(probe,'fn digest('))
assert compact(gen)==compact('core::array::from_fn(|i|M31((seed+17*i as u32+1)%P))')
request=(R/'tools/r1-cost-probe/src/bin/pv_client_gate.rs').read_text()
request_line=next(l for l in request.splitlines() if 'let q = json!({"action":"prove"' in l)
keys=re.findall(r'"([a-z_]+)":',request_line)
assert keys==['action','pool','mint','payer','registry','verifier','note','withdrawal',
    'destination','checkpoint','lane_bytes','checkpoint_bytes','proof_dir','proof_accounts',
    'public_account','verifier_checkpoint']
assert 'q["recipient' not in plan and 'q["owner_key' not in plan and 'q["salt' not in plan
sources=json.loads((R/'evidence/pv-l2c-20261028/resume-d369/focused-project-sources.json').read_text())
emitted=sources['AspisR1TerminalDecoder.Funs']
assert len(re.findall(r'let o\d* ← aspis_core.field.M31.from_le_bytes',
    emitted[emitted.index('def atomic_statement.decode_digest_canonical'):emitted.index('/-- [aspis_statement::pool_v1::format::POOL_V1_DIGEST_ENCODING_VERSION]')]))==8
paths=['tools/r1-cost-probe/src/bin/devnet_spend.rs','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs',
    'tools/r1-cost-probe/src/bin/pv_client_gate.rs','crates/aspis-r1-cost-probe/src/RealR1_client.rs',
    'crates/aspis-core/src/field.rs','crates/aspis-core/src/field/ct.rs',
    'crates/aspis-statement/src/atomic_statement.rs','crates/aspis-statement/src/spend.rs',
    'crates/aspis-statement/src/poseidon2.rs','crates/aspis-statement/src/pool_v1/pair_forest_accounts.rs',
    'crates/aspis-statement/src/pool_v1/incremental_merkle.rs',
    'crates/aspis-statement/src/pool_v1/pair_forest_trace.rs',
    'crates/aspis-pool-wallet-v1/src/live_pool_witness_adapter_v2.rs',
    'crates/aspis-pool-wallet-v1/src/lib.rs']
pins={}
for p in paths:
    current=(R/p).read_bytes()
    base=subprocess.check_output(['git','show','3197fab0eb:'+p],cwd=R)
    assert current==base,p
    pins[p]={'sha256':hashlib.sha256(current).hexdigest(), 'unchanged_from_entry':True}
out={'revision':subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),
    'classification':'script-checked codec/generator source association; not full route structural proof',
    'pins':pins,'request_keys':keys,'scalar_body_sha256':sha(scalar),'digest_body_sha256':sha(digest),
    'generator_body_sha256':sha(gen),'terminal_decoder_emission_sha256':sha(emitted),
    'theorems':['PV_L2C_DecodeRange.scalar_result','PV_L2C_DecodeRange.scalar_success',
        'PV_L2C_DecodeRange.rejects_P','PV_L2C_DigestRange.digest_success',
        'PV_L2C_GeneratedRange.remainder_result','PV_L2C_GeneratedRange.remainder_range'],
    'axioms':'see raw compile receipts 50303,50306,50307; no Kani credit',
    'differences':['M31 newtype erased to U32 in extraction',
        'Rust Option::ok_or and ? retained as complete nested Result/control-flow branches',
        'generator theorem covers final remainder on arbitrary prior U32; seed arithmetic not assumed unbounded'],
    'remaining':['account codec composition','hash-output native association','compiler and mask canonical preservation']}
(E/'decoder-source-check.json').write_text(json.dumps(out,indent=2)+'\n')
print('Checked scalar body, all eight native digest limbs, exact generator copy, JSON field inventory and',len(pins),'unchanged implementation files')
