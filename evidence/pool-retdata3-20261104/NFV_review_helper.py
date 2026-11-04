"""Check exact helper substitution and every intended failing control."""
from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent
p=json.loads((E/'NFV_K061-shape.json').read_text());source=p['source']
original=json.loads((E.parent/'pool-retdata2-20261104/NFR_C_SOURCE_CUT.json').read_text())['encoder_helper']
body=original[original.index('    Ok(Box::new('):original.rindex('}')]
start=source.index('    Ok(allocate(');end=source.index('\n}\n',start)+1
observed=source[start:end]
restored=observed.replace('allocate(','Box::new(').replace('encode(result)','encode_pool_v1_pair_forest_terminal_result_v1(result)')
assert restored==body
assert p['erasure_exact'] and p['body_sha256']==hashlib.sha256(body.encode()).hexdigest()
assert source.count('let actual=helper(&original,')==1
assert 'A:FnOnce([u8;792])->Box<[u8;792]>' in source
assert 'E:FnOnce(&PoolV1PairForestTerminalResultV1)->Result<[u8;792],PoolV1PairForestTerminalFormatErrorV1>' in source
assert 'let boxed=Box::new(bytes);allocation=boxed.as_ptr();boxed' in source
assert not re.search(r'\bstatic\s+mut\b|\btransmute\b|\brepr\s*\(\s*C',source)
assert 'terminal_result_bytes_box_v1(&r)' not in source # excluded K060 actual encoder-loop form
controls=[]
for a,needle in [(62,'boxed[j] == (byte ^ 1)'),(63,'error != PoolV1ProgramError::InvalidVerifierReturnData.into()'),(64,'core::ptr::eq(arg, ptr)'),(65,'boxed.as_ptr() == allocation')]:
 attempt=f'NFV_K{a:03}';s=(E/attempt/'stdout.log').read_text();r=json.loads((E/attempt/'receipt.json').read_text())
 assert r['exit_status']==1 and 'timed out' not in s.lower() and 'unwinding assertion' not in s
 failed=s[s.rfind('Failed Checks:'):];assert needle in failed,attempt
 controls.append(dict(attempt=attempt,intended=needle,failed_as_intended=True))
r=json.loads((E/'NFV_K061/receipt.json').read_text());assert r['exit_status']==0
out=dict(status='PASS local one-call body association under ruling(y)',frozen_body_sha256=hashlib.sha256(body.encode()).hexdigest(),erasure_byte_identical=True,full_typed_result=True,error_variant_coverage='NFV_HELPER_ERROR_COVERAGE.json',native_positive='NFV_K061',controls=controls,lean_erasure='NFV_HelperModel.erase',lean_same_domain='NFV_HelperModel.same_emission',lean_attempt='NFV_B003',trust='P6/D188 native-contract semantic transport RECLASSIFICATION; retained std/Allocator/Box realization; no added row',scope='post-admission production-helper source-cut association only; account/context admission remains B')
(E/'NFV_HELPER_REVIEW.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(dict(status=out['status'],controls=len(controls))))
