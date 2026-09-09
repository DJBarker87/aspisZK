#!/usr/bin/env python3
"""Apply scoped, recorded integration to a copied cached NUC build, never a worktree."""
from pathlib import Path
import hashlib,json,re,shutil
D=Path(__file__).resolve().parent;R=D.parents[2];E=R/'docs/research/v8-no-work-100-20260907/experiments'
assert str(R)=='/home/dombarker/project-offloads/aspis-v8-positive-complete-20260909' and not (R/'.git').exists()
ids=json.loads((D/'identities.json').read_text())['programs_and_accounts'];old=json.loads((R/'docs/research/v8-isolated-devnet-smoke-20260909/identities.json').read_text())['programs_and_accounts']
changes={}
def write(p,s):
 b=p.read_bytes();p.write_text(s);changes[str(p.relative_to(R))]={'before':hashlib.sha256(b).hexdigest(),'after':hashlib.sha256(p.read_bytes()).hexdigest()}
def edit(p,a,b):
 s=p.read_text();assert s.count(a)==1,(str(p),a[:70],s.count(a));write(p,s.replace(a,b))
for p in (D/'upstream').glob('*.rs'):write(E/p.name,p.read_text()) if (E/p.name).exists() else shutil.copy(p,E/p.name)
parent=bytes([121,147,51,56,96,194,205,16,170,24,62,117,31,39,16,186,39,155,51,42,187,191,221,206,119,59,50,23,103,240,1,186])
profile=b'aspis:research:v8:positive-transfer:qm31-q22:asq8-asf8-asr8:v1'
release=b'aspis:research:v8:positive-transfer:lane94:mask3802:40282:image:shifted-rows:complete-v1'
s=(E/'complete_binding.rs').read_text()
for n,pre in [('PROFILE',profile),('RELEASE',release)]:
 s=re.sub(r'(pub const V7_POOL_PAIR_FOREST_TAG73_'+n+r'_BINDING_PREIMAGE: &\[u8\] = )b"[^"]*";',lambda m:m[1]+'b"'+pre.decode()+'";',s)
 s=re.sub(r'(pub const V7_POOL_PAIR_FOREST_TAG73_'+n+r'_BINDING: \[u8;32\] = )\[[^;]+\];',lambda m:m[1]+str(list(hashlib.sha256(pre).digest()))+';',s)
write(E/'complete_binding.rs',s)
# Bind the prior COMPLETE profile as parent (the standalone opt-in host used the V7 default).
# Mask inventories/cell/descriptor layout are retained; outer Registry bindings are new.
p=E/'positive_transfer.rs';s=p.read_text().replace('d.extend(V7_POOL_PAIR_FOREST_TAG73_PROFILE_BINDING);','d.extend('+str(list(parent))+');')
desc=b'AV8/positive-transfer/active-cell-overwrite/lane94/v1'+parent+(1014).to_bytes(2,'little')+bytes([3,94])+bytes.fromhex('f9daf3d54f4285d1')[::-1]+bytes.fromhex('6b661245a56c7189')[::-1]+(3802).to_bytes(2,'little')
assert len(desc)==107
s=s.replace('pub fn descriptor()->Vec<u8>{','pub const FROZEN_DESCRIPTOR: [u8;107] = '+str(list(desc))+';\n#[cfg(v8_performance_sbf)]\npub fn descriptor()->Vec<u8>{ FROZEN_DESCRIPTOR.to_vec() }\n#[cfg(not(v8_performance_sbf))]\npub fn descriptor()->Vec<u8>{')
s=s.replace('    d\n}', '    assert_eq!(d,FROZEN_DESCRIPTOR); d\n}')
s=s.replace('use aspis_statement::{pool_v1::*, StateOnlyTraceFoundation};','use aspis_statement::pool_v1::*;\n#[cfg(not(v8_performance_sbf))] use aspis_statement::StateOnlyTraceFoundation;')
for fn in ['pub fn mask_cells()', 'fn fingerprint(', 'pub fn install(']:s=s.replace(fn,'#[cfg(not(v8_performance_sbf))]\n'+fn)
write(p,s)
p=E/'performance.rs';s=p.read_text();s=s.replace('use super::*;', 'use super::*;\n#[path="../../v8-positive-complete-devnet-20260909/live_context.rs"] mod live_context;',1)
s=s.replace('let(public,witness,mut snapshot)=we::fixture();','let(public,witness,mut snapshot)=if std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_some(){live_context::load()}else{we::fixture()};')
s=s.replace('let mut runtime=provision_accounts(&witness);','let mut runtime=provision_accounts(&witness);\n    if std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_some(){assert_eq!(runtime.anchor_root,public.anchor_root);runtime.pool=public.pool;runtime.deployment_domain=public.deployment_domain;runtime.anchor_sequence=public.anchor_sequence;}')
s=s.replace('let complete_context=','let mut complete_context=')
s=s.replace('assert!(complete_context.is_none(),"new positivity profile is not integrated with complete transaction wrapper");','assert!(matches!(payment,PoolV1PairForestTerminalPaymentV1::PrivateTransfer(_)),"transfer-only profile");')
s=s.replace('    #[cfg(v8_positive_transfer)] let positive_case=', '    if let Some((statement,_))=&complete_context{assert_eq!(compiled.public_statement,statement.common().lane_transition); }\n    #[cfg(v8_positive_transfer)] let positive_case=')
s=s.replace('let transition=compiled.public_statement;', '''let transition=compiled.public_statement;
    #[cfg(v8_positive_transfer)] if let Some((statement,attempt))=&mut complete_context {
        let PoolV1PairForestTerminalPaymentV1::PrivateTransfer(p)=payment else{panic!("transfer only")};
        let mut common=*statement.common();common.lane_transition=transition;
        *statement=PoolV1PairForestTerminalStatementV1::PrivateTransfer{public:p,common};
        let sb=encode_pool_v1_pair_forest_terminal_statement_v1(statement).unwrap();
        let digest=v7_pool_pair_forest_tag73_statement_digest_v1(&sb,hash);
        let dir=std::env::var("ASPIS_V8_COMPLETE_CONTEXT").unwrap();
        let vk:[u8;32]=std::fs::read(format!("{dir}/verifier.bin")).unwrap().try_into().unwrap();
        let pk:[u8;32]=std::fs::read(format!("{dir}/proof-account.bin")).unwrap().try_into().unwrap();
        *attempt=complete_binding::bind_attempt(hash,&digest,&vk,&pk);
        std::fs::write(format!("{out}/statement.bin"),sb).unwrap();
    }''')
s=s.replace('    for seed in seeds {','    assert!(std::env::var_os("ASPIS_V8_MAX_FRONTIER_SCAN").is_none());\n    for seed in seeds {')
s=s.replace('            continue;','            std::fs::write(format!("{out}/proof-{seed}.bin"),&body).unwrap();\n            continue;')
write(p,s)
# Rebind capabilities to new isolated program identities.
def key(s):
 n=0
 for c in s:n=n*58+'123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'.index(c)
 return '['+','.join(map(str,n.to_bytes(32,'big')))+']'
p=R/'programs/aspis-verifier/src/v7_pair_forest_dispatch.rs'
edit(p,key(old['pool']),key(ids['pool']))
# The existing Registry image is intentionally retained.
assert ids['registry']==old['registry']
# Existing lifecycle code is identical, now sourced from this integration directory.
p=R/'programs/aspis-verifier/src/lib.rs';write(p,p.read_text().replace('v8-isolated-devnet-smoke-20260909/proof_lifecycle.rs','v8-positive-complete-devnet-20260909/proof_lifecycle.rs'))
# Build flags explicitly select the repaired profile. Frozen source checker remains archived,
# but cannot authenticate changed sources; this manifest pins the changed inputs instead.
p=E/'run_complete_build_nuc.sh';s=p.read_text().replace("readonly common='", "readonly common='--cfg v8_positive_transfer ")
s=s.replace('terminal-prefix|terminal-fixed|terminal-fused|terminal-stack) bash "$complete_exp/check_terminal_query_sources.sh" "$mode";;','terminal-prefix|terminal-fixed|terminal-fused|terminal-stack) python3 "$complete_root/docs/research/v8-positive-complete-devnet-20260909/check_inputs.py";;')
write(p,s)
# Fixture driver uses the same new identities, with predeclared zero-output variants.
p=R/'results/v7-pair-forest-combined-rejection-litesvm-20260828/harness/src/main.rs';s=p.read_text()
s=s.replace('const COMPUTE_UNIT_LIMIT: u32 = 1_400_000;', 'const COMPUTE_UNIT_LIMIT: u32 = 1_200_000;')
s=re.sub(r'const POOL_PROGRAM_BYTES: \[u8; 32\] = \[0x41; 32\];','const POOL_PROGRAM_BYTES: [u8;32] = '+key(ids['pool'])+';',s)
s=re.sub(r'const REGISTRY_PROGRAM_BYTES: \[u8; 32\] = \[0x44; 32\];','const REGISTRY_PROGRAM_BYTES: [u8;32] = '+key(ids['registry'])+';',s)
s=re.sub(r'const VERIFIER_PROGRAM_ID: &str = "[^"]+";', 'const VERIFIER_PROGRAM_ID: &str = "'+ids['verifier']+'";',s)
s=s.replace('let recipient = pool_v1_note_commitment(&digest(300), 600, asset_id, &digest(400));','let case=env::var("ASPIS_V8_POSITIVE_CASE").unwrap_or_else(|_|"honest".into());\n    let (rv,cv)=match case.as_str(){"honest"=>(600,400),"recipient_zero"=>(0,1000),"change_zero"=>(1000,0),_=>panic!("unknown case")};\n    let recipient = pool_v1_note_commitment(&digest(300), rv, asset_id, &digest(400));')
s=s.replace('let change = pool_v1_note_commitment(&digest(500), 400, asset_id, &digest(600));','let change = pool_v1_note_commitment(&digest(500), cv, asset_id, &digest(600));')
s=s.replace('if args.scenario == Scenario::ProofRejection {','if args.scenario == Scenario::ProofRejection && case=="honest" {')
write(p,s)
(D/'integration-inputs.json').write_text(json.dumps(changes,indent=2)+'\n')
(D/'profile.json').write_text(json.dumps({'profile_preimage':profile.decode(),'profile_sha256':hashlib.sha256(profile).hexdigest(),'release_preimage':release.decode(),'release_sha256':hashlib.sha256(release).hexdigest(),'descriptor_hex':desc.hex(),'descriptor_sha256':hashlib.sha256(desc).hexdigest(),'transfer_only':True,'privacy_claim':'experimental; changed full-view masking not proved'},indent=2)+'\n')
print('Integrated repaired semantic profile, static checked descriptor, live context binding and matched local driver.')
