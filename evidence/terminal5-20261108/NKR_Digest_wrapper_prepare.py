from pathlib import Path
import subprocess,re,json,hashlib,difflib
E=Path(__file__).resolve().parent;rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';source='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs';old=subprocess.check_output(['git','show',rev+':'+source],text=True);code=(E/'NKR_Digest_wrapper_window.rs.txt').read_text()
start=old.index('fn public_digest_packed(');end=old.index('\n}',start)+2;body=old[start:end]
assert 'return public_digest_packed_selector_tensor(public, openings, selectors);' in body
assert re.search(r'fn NKR_Digest_warg_wrapper\([^\n]+\{return NKR_Digest_warg_child\(public,openings,selectors,l\);\}',code)
assert 'static mut' not in code
name='crates/aspis-statement/src/pool_v1/NKR_Digest_wrapper_window.rs';new=old+'\n#[cfg(kani)]\n#[path="NKR_Digest_wrapper_window.rs"]\nmod NKR_Digest_wrapper_window;\n'
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+source,tofile='b/'+source))+''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
(E/'NKR_Digest_wrapper_window.patch').write_text(patch)
(E/'NKR_Digest_WRAPPER_WINDOW_ERASURE.json').write_text(json.dumps(dict(revision=rev,source=source,body=body,source_sha256=hashlib.sha256(old.encode()).hexdigest(),harness_sha256=hashlib.sha256(code.encode()).hexdigest(),deployed_feature='pool-v1-pair-forest-packed-digest-selector-tensor-audit',identity=True,scope='actual literal wrapper, one universally selected projected payload component plus full2cell reply; all inputs arbitrary flat; no full-record log copy',retired='K022 wholewrapper timeout',negative='invert same selected component assertion'),indent=1))
print('NKR actual wrapper25component projected argument/2reply window identity PASS')
