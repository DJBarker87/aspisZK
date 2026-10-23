#!/usr/bin/env python3
"""Smallest failed containment check; no Rust/Lean execution claim."""
import hashlib,json,re,resource,subprocess,sys,time
from pathlib import Path
start=time.monotonic()
R=Path(__file__).resolve().parent.parent
source=Path('crates/aspis-prover/src/state_only_entropy.rs').read_text()
domain=re.search(r'const POOL_V1_SOURCE_SEED_DOMAIN: &\[u8\] = b"([^"]+)";',source)[1].encode()
model=Path('docs/research/v8-r0-zk-20261009/lean/R1Z/LayoutR1PBin.lean').read_text()
model_domain=bytes(map(int,re.search(r'def dSourceSeed : List UInt8 := \[([^\]]+)\]',model)[1].split(',')))
assert domain==model_domain
# A public byte-blind adversary fixes this query before the private draw.
# E1 allows a nonzero raw seed equal to this guess. This is a carrier sample,
# not a constructed complete actual realBad-free prover execution.
seed=bytes([1])*32; simulator_seed=bytes([2])*32
public_frame=bytes(32+156) # arbitrary public bytes; head/suffix proof works for every frame
query=domain+public_frame+seed
private_memo=query[-32:]==seed
simulator_guess=query[:52]==b'UNPROVED:R1:SIM:COIN'+simulator_seed
fuel_exhausted=all(bytes([1])*32==bytes(32) for _ in range(5))
passed=(not private_memo) or simulator_guess or fuel_exhausted
usage=resource.getrusage(resource.RUSAGE_SELF)
record=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
            source_sha256=hashlib.sha256(source.encode()).hexdigest(),domain_ascii=domain.decode(),
            query_hex=query.hex(),private_seed_hex=seed.hex(),simulator_seed_hex=simulator_seed.hex(),
            private_memo=private_memo,simulator_seed_guess=simulator_guess,five_draw_fuel_exhausted=fuel_exhausted,
            expected_exit_status=1,exit_status=0 if passed else 1,wall_seconds=time.monotonic()-start,
            peak_rss_kib=usage.ru_maxrss//1024 if sys.platform=='darwin' else usage.ru_maxrss,swaps=usage.ru_nswap,
            scope='Fails privateMemo implies simulator seed or five-draw fuel. Does not falsify RunJoin, establish actual realBad absence, or discharge E1 adaptive marginals.',
            next='Prove agreement on private-memo/zero paths within the fixed events, or explicitly compose an approved changed envelope. No ledger collision charge.',
            print_axioms='N/A static byte-frame check; formal analogue RealR1_EventBoundary.fixed_extension_misses')
(R/'event-gate.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:record[k] for k in ['exit_status','private_memo','simulator_seed_guess','five_draw_fuel_exhausted']}))
sys.exit(record['exit_status'])
