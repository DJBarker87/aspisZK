from pathlib import Path
import NCP_runner as m
m.admit('NCP_EXTRACT3_UPLOAD')
# Byte-identical reference definitions, copied into extraction-only module; no harness rename.
exact=(m.E/'NCP_exact.rs.txt').read_text().splitlines()[1]
canon=(m.E/'NCP_scalar.rs.txt').read_text().splitlines()[2]
refs='use crate::pool_v1::pair_terminal::PoolV1PairVerifierTransportErrorV1;\nuse crate::poseidon2::Digest;\n'+exact+'\n'+canon+'\n'
(m.E/'NCP_refs.rs.txt').write_text(refs)
old=(m.E/'NCP_extract_host.py').read_text()
# Host script most recently written by X002; use its pinned tool invocations, changed roots/namespace/output.
script=old.replace('crate::NCP_digest::NCP_ref_decode','crate::NCP_refs::NCP_exact_ref').replace("'--dest-file'","'--start-from','crate::NCP_refs::NCP_canon','--dest-file'").replace('NCP_decode_v2.llbc','NCP_helpers.llbc').replace('NCP_extracted_v2','NCP_helpers_extracted').replace('NCP_Extracted2','NCP_HelperExtracted').replace('NCP_EXTRACTION2_TOOL_PINS','NCP_EXTRACTION3_TOOL_PINS').replace('NCP_EXTRACTION2_OUTPUT_PINS','NCP_EXTRACTION3_OUTPUT_PINS')
(m.E/'NCP_extract_helpers_host.py').write_text(script)
r=m.py(f'''from pathlib import Path
b=Path({m.B!r});p=b/'NCP_src/crates/aspis-statement/src/lib.rs';p.write_text(p.read_text()+'\\n#[cfg(ncp_extract)] pub mod NCP_refs;\\n')
(b/'NCP_src/crates/aspis-statement/src/NCP_refs.rs').write_text({refs!r});(b/'NCP_extract_helpers_host.py').write_text({script!r})
''');assert r.returncode==0,r.stderr
r=m.launch('NCP_X003','extraction',['python3',m.B+'/NCP_extract_helpers_host.py'],['NCP_extract_helpers_host.py','NCP_src/crates/aspis-statement/src/NCP_refs.rs','NCP_src/crates/aspis-statement/src/lib.rs'],540)
print((m.E/'NCP_X003/stdout.log').read_text()[-5000:])
