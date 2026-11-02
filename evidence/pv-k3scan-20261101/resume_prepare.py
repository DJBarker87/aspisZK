from pathlib import Path
import subprocess,hashlib,json
E=Path(__file__).resolve().parent;P=E/'rerun-reserve';P.mkdir(exist_ok=True)
manifest=subprocess.check_output(['git','show','4bc172e539c065040181e74fc281135f73e422ec:tools/pv-cb-20261026/proof/Cargo.toml'])
assert hashlib.sha256(manifest).hexdigest()=='13d113bfd2e2df215ea3bb0c570849fa53e9e7e3fa04ed173e053929c816ecd2'
(P/'Cargo.toml').write_bytes(manifest+b'\n[features]\nnegative-overflow=[]\nnegative-small=[]\n')
(P/'Cargo.lock').write_bytes(subprocess.check_output(['git','show','4bc172e539c065040181e74fc281135f73e422ec:tools/pv-cb-20261026/proof/Cargo.lock']))
t=(E/'blobs/ea327083d4f56c536d472604689c49e43b22668a2cf0e54146bd6d8ed504e813.rs').read_text()
old='assert!(actual.try_reserve_exact(usize::MAX).is_err());';new='let result=actual.try_reserve_exact(usize::MAX);\n        if cfg!(feature="negative-overflow") { assert!(result.is_ok()); } else { assert!(result.is_err()); }';assert t.count(old)==1;t=t.replace(old,new)
old='if result.is_ok() { assert!(actual.capacity()>=len+n); }';new='if result.is_ok() { if cfg!(feature="negative-small") { assert!(actual.capacity()<len+n); } else { assert!(actual.capacity()>=len+n); } }';assert t.count(old)==1;t=t.replace(old,new)
(P/'lib.rs').write_text(t);(P/'reference.rs').write_bytes((E/'blobs/531b748550d0ee7df9fb2268d3ed2e97e29dc9e97ffb5dba3de512c6128c2bfa.rs').read_bytes())
(E/'RESUME-D549.json').write_text(json.dumps({'entry':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'next':'K79202','allowance_invocations':60,'already_spent':2,'priority':['V183 installed op32 family','other installed suspended rows','V185','V244 local bodies','V164 V182 V234 V235 qualified packets','rest'],'V183_scope':'Historical bounded std diagnostics, not universal allocator/world refinement. Current installed ReserveSelected.complete is a structural K-1 substitute; its symbolic proof does not consume these Kani diagnostics. No K-1 or std transfer is restored by the new pair.','manifest_original_sha256':hashlib.sha256(manifest).hexdigest(),'changes':'Same complete historical root/reference and package/harness names; only feature-selected assertion inversions and evaluating the overflow call once into result. No new stub or oracle.'},indent=2)+'\n')
