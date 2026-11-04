from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
p='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs';s=subprocess.check_output(['git','show',REV+':'+p],text=True)
a=s.index('pub fn encode_pool_v1_pair_forest_terminal_request_v1(');z=s.index('\n}',a)+2;original=s[a:z]
ref=original.replace('pub fn encode_pool_v1_pair_forest_terminal_request_v1(','pub fn encode_ref(',1)
offsets={}
for name,value in [('REQUEST_PROFILE_OFFSET',8),('REQUEST_RELEASE_OFFSET',40),('REQUEST_POOL_PROGRAM_OFFSET',72),('REQUEST_PAYMENT_OFFSET',104)]:
 actual=int(re.search(r'const '+name+r':\s*usize\s*=\s*(\d+)',s)[1]);assert actual==value
 offsets[name]=value;ref=ref.replace(name,str(value))
ref=ref.replace('.map_err(PoolV1PairForestTerminalFormatErrorV1::Payment)?','.map_err(|e| PoolV1PairForestTerminalFormatErrorV1::Payment(e))?')
ref=ref.replace('request.public.transition_kind() as u8','match request.public { PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_) => 1, PoolV1PairForestTerminalPaymentV1::Withdrawal(_) => 2 }')
(E/'NFV_reference.rs').write_text('use aspis_statement::pool_v1::*;\n'+ref+'\n')
(E/'NFV_reference_Cargo.toml').write_text('''[package]
name="nfv_request_reference"
version="0.1.0"
edition="2021"
[workspace]
[dependencies]
aspis-statement={path="../NFV_src/crates/aspis-statement",features=["pool-v1-kernel"]}
''')
(E/'NFV_REFERENCE_INPUTS.json').write_text(json.dumps(dict(frozen_revision=REV,source=p,source_sha256=hashlib.sha256(s.encode()).hexdigest(),function_sha256=hashlib.sha256(original.encode()).hexdigest(),reference_sha256=hashlib.sha256((E/'NFV_reference.rs').read_bytes()).hexdigest(),offsets=offsets,adaptations=['function renamed encode_ref in separate reference crate','private offsets replaced by checked frozen literal values','map_err constructor expressed as equivalent explicit closure to avoid known translator constructor-coercion collision','inline two-branch transition-kind projection; actual public method is checked below'],scope='small request encoder only; never re-extract the process/HRTB spine'),indent=1)+'\n')
assert 'pub fn transition_kind(&self) -> PoolV1TransitionKind' in s
method=s[s.index('pub fn transition_kind(&self) -> PoolV1TransitionKind'):];method=method[:method.index('\n    }')+6]
assert 'Self::PrivateTransfer(_) => PoolV1TransitionKind::PrivateTransfer' in method
assert 'Self::Withdrawal(_) => PoolV1TransitionKind::Withdrawal' in method
print('Prepared exact small encoder reference; no extraction launched')
