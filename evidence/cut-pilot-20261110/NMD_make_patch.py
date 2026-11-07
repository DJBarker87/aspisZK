from pathlib import Path
import subprocess,json,difflib,hashlib
E=Path(__file__).resolve().parent
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
paths=['crates/aspis-r1-cost-probe/src/lib.rs','crates/aspis-r1-cost-probe/src/candidate.rs','crates/aspis-r1-cost-probe/src/verifier.rs']
original={n:subprocess.check_output(['git','show',frozen+':'+n],text=True) for n in paths};changed=dict(original)
changed[paths[0]]='#![cfg_attr(kani,feature(allocator_api))]\n'+original[paths[0]]
for signature,attrs in json.loads((E/'NMD_ACTUAL_CONTRACTS.json').read_text()).items():
 assert changed[paths[1]].count(signature)==1;changed[paths[1]]=changed[paths[1]].replace(signature,''.join(attrs)+signature,1)
for path,functions in json.loads((E/'NMD_EXTRA_CONTRACTS.json').read_text()).items():
 for signature,attrs in functions.items():
  assert changed[path].count(signature)==1;changed[path]=changed[path].replace(signature,''.join(attrs)+signature,1)
changed[paths[1]]+='\n#[cfg(kani)]\n#[path="NMD_native.rs"]\nmod NMD_native;\n'
changed['crates/aspis-r1-cost-probe/src/NMD_native.rs']=(E/'NMD_actual.rs').read_text()
patch=''.join(''.join(difflib.unified_diff(original.get(n,'').splitlines(True),s.splitlines(True),fromfile='a/'+n if n in original else '/dev/null',tofile='b/'+n)) for n,s in changed.items())
(E/'NMD_HARNESSES.patch').write_text(patch);(E/'NMD_HARNESSES.patch.sha256').write_text(hashlib.sha256(patch.encode()).hexdigest()+'\n')
(E/'NMD_PATCH_README.md').write_text('''# Harness configurations

NMD_HARNESSES.patch is the canonical ACTUAL parser/marker configuration against frozen4bb3b3f5. Apply only in a private scratch copy, together with the exact canonical KMX_copy_stubs.patch. It is not a shipped-source change. The parser contracts have NO passing full-allocation proof; marker has the restricted controlled certificate. Do not use the proposed parser contract as verified evidence.

Shape, constructor, generic-record, ProgramResult and informational K-3 configurations are mutually exclusive private overlays, selected by the NMD_ runners. Every executed configuration is preserved once by content hash in NMD_INPUTS.json/NMD_INPUTS, indexed per attempt. Separate NMD_*.rs templates and scripts reproduce those overlays. No compiler, binary, ELF, object or dependency-source change is committed. NMD_K3_* files are byte-identical imports of the NEF_K002 reproducer with original names; their writable statics are informational only.
''')
print('Canonical scratch harness patch and sha256 recorded')
