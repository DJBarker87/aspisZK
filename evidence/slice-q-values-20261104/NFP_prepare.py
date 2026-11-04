from pathlib import Path
import json,lzma,hashlib
E=Path(__file__).resolve().parent
P=E.parent/'slice-q-mul9-20261104'
# Own runner; inherited launcher remains byte-identical.
s=(P/'NFM_run.py').read_text().replace('NFM_','NFP_').replace('codex-cx-slice-q-mul9-20261104','codex-cx-slice-q-values-20261104').replace('codex-cx-slice-q-mul9-cache-20261104','codex-cx-slice-q-values-cache-20261104')
a=s.index('paths=[');b=s.index('\n# Explicit fixture',a)
s=s[:a]+'''paths=[B+'/NFP_objects',C+'/NFM_exports_20261104',C+'/NFG_exports_20261104',C+'/NFG_NFF_objects',C+'/NFI_exports_20261104',C+'/NFF_exports_20261104',C+'/fixtures',C+'/NER_cohort',C+'/NFE_exports_20261104',C+'/NFC_audit_support_20261104',C+'/NFC_exports_20261104',C+'/NFA_exports_20261104',C+'/NEV_exports_20261104',C+'/NEI_exports_20261103',C+'/NEG_results_20261101',C+'/NEG_exports_20261029',C+'/NEB_exports_20261029',C,W,W+'/objects',T+'/lib/lean']'''+s[b:]
s=s.replace("assert a.startswith('NFP_L') and 1<=int(a[-3:])<=60", "assert (a.startswith('NFP_L') and 1<=int(a[-3:])<=60) or (a.startswith('NFP_K') and 1<=int(a[-3:])<=100)")
s=s.replace("if kind=='lean':", "if kind=='kani':\n files['NFP_gate.py']=(E/'NFP_gate.py').read_text();files['NFP_graph.py']=(E/'NFP_graph.py').read_text();files['NFP_build.py']=(E/'NFP_build.py').read_text();files['NFP_query.rs.txt']=(E/'NFP_query.rs.txt').read_text();files['NFP_KMX.patch']=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text();sources=list(files);command=['python3','NFP_gate.py',a+'.json',target]\n env.update(CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_DEV_OPT_LEVEL='3',CARGO_PROFILE_DEV_DEBUG='0',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1')\n native=['/home/dombarker/.cargo/bin/cargo-kani','kani','--manifest-path',B+'/NFP_src/crates/aspis-r1-cost-probe/Cargo.toml','--target-dir',B+'/NFP_target','--lib','--features','private-leaf-salts,optimized-terminal,program-build','-j','1','-Z','unstable-options','-Z','stubbing','--harness-timeout','90s','--exact','--harness','verifier::candidate::NFP_query::'+target,'--output-format','terse']\n cfg_native=native\nelif kind=='lean':")
s=s.replace("files[a+'.json']=json.dumps(cfg)","\nif kind=='kani':cfg['native_command']=cfg_native\nfiles[a+'.json']=json.dumps(cfg)")
s=s.replace("for module in ([", "for module in ([")
# Existing pin loop inspects first source imports, harmless for python source.
s=s.replace("+[a+'.json']", "+[a+'.json']+[str(p.relative_to(b)) for p in b.glob(a+'-*.json')]")
s=s.replace("if kind=='auditbin':\n import lzma", "if kind=='auditbin':\n import lzma")
(E/'NFP_run.py').write_text(s)
(E/'NFP_graph.py').write_text((P/'NFM_graph.py').read_text().replace('NFM_','NFP_'))
print('prepared own runner')
