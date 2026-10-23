#!/usr/bin/env python3
"""Actual SDK context instantiates ordered copy/owner/guard contracts.
Ordinary proof checks every verified leaf precondition and caller outcome;
it does NOT enforce or assume the timed-out enclosing DFCC frame. The exact
leaf footprint union needs a separate composition/actual-source certificate.
"""
from pathlib import Path
import subprocess,json,hashlib,sys
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);assert not O.exists()
subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/prepare-sdk-modular-ordered-tail.py'),str(O)],check=True)
p=O/'src/lib.rs';s=p.read_text();s=s.replace('#[kani::proof_for_contract(native_finish_drop_chain)] #[kani::unwind(1772)]','#[kani::proof] #[kani::unwind(48)]')
needle=' kani::cover!(actual_result.is_ok(),';assert s.count(needle)==1
s=s.replace(needle,''' assert_eq!(actual_result.is_ok(),expected_status==0,"ordered actual SDK caller preserves success condition");
 assert_eq!(matches!(actual_result,Err(ProgramError::InvalidAccountData)),expected_status==1,"ordered actual SDK caller preserves exact length error");
 assert_eq!(matches!(actual_result,Err(ProgramError::InvalidInstructionData)),expected_status==2,"ordered actual SDK caller preserves mapped first error");
 assert_eq!(unsafe{(*destination)[observed]},expected_byte,"ordered actual SDK caller saves exact selected checkpoint byte");
'''+needle)
p.write_text(s);p=O/'Cargo.toml';p.write_text(p.read_text().replace('modular-ordered-tail-v3','ordered-tail-links-v1'))
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=hashlib.sha256(s.encode()).hexdigest(),qualification=__doc__,remaining='Must pass every safety, leaf precondition, caller result/byte/counter assertion and source covers. Reuse matching owner-step, exact copy and original guard certificates. Source compiler-cleanup equivalence, frozen allocator/owner/runtime/ABI and leaf footprint union/source composition remain. No enclosing frame is assumed or claimed; no whole S2.'),indent=2)+'\n')
