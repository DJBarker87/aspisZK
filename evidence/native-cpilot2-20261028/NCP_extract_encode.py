from pathlib import Path
import NCP_runner as m
m.admit('NCP_EXTRACT4_UPLOAD')
s=(m.E/'NCP_digest.rs.txt').read_text();start=s.index('pub fn NCP_ref_encode');end=s.index('\npub fn NCP_ref_decode',start);definition=s[start:end]
(m.E/'NCP_encode_reference.rs.txt').write_text(definition+'\n')
old=(m.E/'NCP_extract_helpers_host.py').read_text();script=old.replace("'--start-from','crate::NCP_refs::NCP_canon',",'').replace('crate::NCP_refs::NCP_exact_ref','crate::NCP_refs::NCP_ref_encode').replace('NCP_helpers.llbc','NCP_encode.llbc').replace('NCP_helpers_extracted','NCP_encode_extracted').replace('NCP_HelperExtracted','NCP_EncodeExtracted').replace('NCP_EXTRACTION3_TOOL_PINS','NCP_EXTRACTION4_TOOL_PINS').replace('NCP_EXTRACTION3_OUTPUT_PINS','NCP_EXTRACTION4_OUTPUT_PINS')
(m.E/'NCP_extract_encode_host.py').write_text(script)
r=m.py(f'''from pathlib import Path
b=Path({m.B!r});p=b/'NCP_src/crates/aspis-statement/src/NCP_refs.rs';p.write_text(p.read_text()+{definition!r}+'\\n');(b/'NCP_extract_encode_host.py').write_text({script!r})
''');assert r.returncode==0,r.stderr
r=m.launch('NCP_X004','extraction',['python3',m.B+'/NCP_extract_encode_host.py'],['NCP_extract_encode_host.py','NCP_src/crates/aspis-statement/src/NCP_refs.rs','NCP_src/crates/aspis-statement/src/lib.rs'],540)
print((m.E/'NCP_X004/stdout.log').read_text()[-4000:])
