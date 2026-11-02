from pathlib import Path
import subprocess,json,hashlib,lzma,base64
E=Path(__file__).resolve().parent;P=E/'v185-source';P.mkdir(exist_ok=True)
rev='bd47052f039ae2d96060acb5607fe652ebe193d4';ref='ea4eca5b147920a19ccde05e2cc95c4d2bad25c8';s=json.loads(subprocess.check_output(['git','show',ref+':evidence/pv-cblib-20261027/candidate-snapshot.json']))
records=[]
for name,h in s['files'].items():
 b=subprocess.check_output(['git','show',rev+':'+name]);assert hashlib.sha256(b).hexdigest()==h,name
 p=P/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b);records.append({'path':name,'sha256':h,'source':rev+':'+name})
p=P/'crates/aspis-r1-cost-probe/src/host_commitment.rs';b=(E/'blobs/6b20632e53254da24e5c542acb93b2f31d959b312ac735807a12beaf2d69ab72.rs').read_bytes();p.write_bytes(b)
t=b.decode();old='assert_eq!(v.is_empty(), empty_reference(&v));';assert t.count(old)==1;t=t.replace(old,'if cfg!(feature="negative-op34") { assert_ne!(v.is_empty(), empty_reference(&v)); } else { '+old+' }');p.write_text(t)
p=P/'crates/aspis-r1-cost-probe/Cargo.toml';t=p.read_text();assert '[features]' in t;t=t.replace('[features]','[features]\nnegative-op34=[]',1);p.write_text(t)
(E/'V185-SOURCE-CLOSURE.json').write_text(json.dumps({'historical_command_manifest':'source/crates/aspis-r1-cost-probe/Cargo.toml','snapshot_record':ref+':evidence/pv-cblib-20261027/candidate-snapshot.json','snapshot_revision':rev,'files':records,'harness_override_sha256':hashlib.sha256(b).hexdigest(),'unused_missing_input':'kani-proof/lib.rs is outside the manifest-selected library/dependencies: selected library has default src/lib.rs, no [lib] path override, no kani-proof dependency, no module declaration importing it. Missing unrelated standalone input remains historically unrecovered; not silently replaced.','changes':['negative-op34 feature and exact selected assertion inversion only'],'scope':'Original full crate and candidate dependency workspace, no mocked Word/Error or narrowed vectors; original all errors/both Word variants/length0..2.','transfer':'Historical host-prover features preserved; no verifier deployed feature or std-parity transfer claimed.'},indent=2)+'\n')
# Capture transfer payload, not an additional checked-in expanded workspace.
payload={str(p.relative_to(P)):base64.b64encode(p.read_bytes()).decode() for p in P.rglob('*') if p.is_file()};raw=json.dumps(payload).encode();(E/'V185-source.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'V185-source.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(len(records),'hash-checked snapshot files',len(raw),'payload bytes')
