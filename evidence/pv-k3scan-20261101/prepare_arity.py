from pathlib import Path
import subprocess,json,lzma,base64,hashlib,re
E=Path(__file__).resolve().parent;REV='f3071faf749b28cf563e25984728489a29d52c79';sha=lambda b:hashlib.sha256(b).hexdigest();base='tools/prover-rw-20261023/pv-rw21/proof/'
def git(p):return subprocess.check_output(['git','show',REV+':'+p],stderr=subprocess.DEVNULL)
paths=subprocess.check_output(['git','ls-tree','-r','--name-only',REV,'Cargo.toml','Cargo.lock','crates/aspis-core','crates/aspis-statement'],text=True).splitlines();files={n:git(n)for n in paths}
# Complete extra literal/build includes from the historical source revision.
for rec in json.loads((E/'V185-PREFLIGHT-REPAIR.json').read_text())['files']:
 n=rec['path']
 if '/c3/'not in n:files[n]=git(n)
s=(E/'blobs/64c3d130b53158db6c0dcc95154acc91b6c62df62a8b55585a9c162ad510378e.rs').read_text();start=s.index('#[kani::proof]');end=s.index('#[kani::proof]',start+1);selected=s[:start]+s[start:end]
old='assert_eq!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda));';assert selected.count(old)==1
selected=selected.replace(old,'if cfg!(feature="negative-arity0") { assert_ne!(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda),indexed(tag,&values,lambda)); } else { '+old+' }')
files[base+'small.rs']=selected.encode();files[base+'lib.rs']=b'#[cfg(kani)] mod small;\n';files[base+'Cargo.toml']=git(base+'Cargo.toml')+b'\n[features]\nnegative-arity0=[]\n'
assert sha(files['crates/aspis-statement/src/logup.rs'])=='c6e84617e6473f014fc53c704dd26b04667046211985ea6ddca8f66f496bea65'
t=files['Cargo.toml'].decode();t=re.sub(r'members\s*=\s*\[.*?\]','members=["crates/aspis-core","crates/aspis-statement"]',t,count=1,flags=re.S);files['Cargo.toml']=t.encode()
raw=json.dumps({n:base64.b64encode(b).decode()for n,b in files.items()}).encode();(E/'Arity-source.json.xz').write_bytes(lzma.compress(raw,preset=6));(E/'Arity-source.json.sha256').write_text(sha(raw)+'\n')
(E/'ARITY-SOURCE-CLOSURE.json').write_text(json.dumps({'credit':'C135','revision':REV,'original_selected_module_sha256':'64c3d130b53158db6c0dcc95154acc91b6c62df62a8b55585a9c162ad510378e','selected_property':'small::source_p6_arity0','shape':'Zero-length values. The source and reference loops execute zero iterations, hence no field-multiplication chain is reached. Arbitrary raw tag and lambda unchanged. No retry of SAT-hard nonempty multiplication chain.','projection':'Original helpers and original arity0 property; unselected inherited/full-arity/literal tests omitted, no function/module renamed.','control':'Invert only original equality, feature-selected','current_scope':'V164 qualified restoration is structural and independent; this is a bounded historical-support check only.'},indent=2)+'\n')
print(len(files),'frozen files')
