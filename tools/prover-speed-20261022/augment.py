#!/usr/bin/env python3
"""Add missing semantic subphases after initial instrumentation preflight."""
from pathlib import Path
import sys,re
R=Path(sys.argv[1]);B=R/'crates/aspis-r1-cost-probe/src'
for file,fn,label in [('host_sumcheck.rs','prove_sumcheck','semantic_sumcheck'),('host_semantic.rs','point_claims','semantic_point_claims')]:
 p=B/file;s=p.read_text();m=re.search(r'\bfn '+fn+r'\b',s);at=s.index('{',m.end())+1;s=s[:at]+'\nlet _speed_guard = crate::speed_prof::span("'+label+'");\n'+s[at:];p.write_text(s)
p=B/'host_semantic.rs';s=p.read_text();a='let terminal = public.terminal_qm31(&claims, point, &challenges).map_err(|_|Error::Public)?;';assert s.count(a)==1;s=s.replace(a,'let terminal = {let _g=crate::speed_prof::span("semantic_terminal");public.terminal_qm31(&claims, point, &challenges).map_err(|_|Error::Public)?};');p.write_text(s)
p=B/'prover.rs';s=p.read_text();a='let d: [K;1024]=reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,context).map_err(mask_error)?.try_into().map_err(|_|Error::Semantic)?;';assert s.count(a)==1;s=s.replace(a,'let d: [K;1024]={let _g=crate::speed_prof::span("profile21_d");reserved.derive_pool_v1_pair_forest_zero_factor_d(hash,context).map_err(mask_error)?.try_into().map_err(|_|Error::Semantic)?};');p.write_text(s)
p=R/'crates/aspis-prover/src/state_only_entropy.rs';s=p.read_text();start=s.index('    pub fn reserve_and_build_pool_v1_pair_forest_mask_material_v1(');end=s.index('\n}\n',start);a=s[start:end];x='        if !nonce_store.reserve(context.statement_digest, context.mask_nonce) {';assert a.count(x)==1;a=a.replace(x,'        let speed_reserve=std::time::Instant::now();\n'+x);x='        let mut pre_reserved = PreReservedNonce {';assert a.count(x)==1;a=a.replace(x,'        std::eprintln!("SPEED_RESERVATION {}",speed_reserve.elapsed().as_secs_f64());\n'+x);s=s[:start]+a+s[end:];p.write_text(s)
