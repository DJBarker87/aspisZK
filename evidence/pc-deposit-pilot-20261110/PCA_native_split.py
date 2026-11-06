from pathlib import Path
import json,base64,lzma,hashlib,difflib
E=Path(__file__).resolve().parent
old=json.loads((E/'PCA_NATIVE_PATCH_META.json').read_text());(E/'PCA_K002_HARNESS_META.json').write_text(json.dumps(old,indent=1)+'\n')
x=json.loads(lzma.decompress((E/'PCA_NATIVE_FROZEN_INPUTS.json.xz').read_bytes()));source=base64.b64decode(x['programs/aspis-pool/src/pair_forest.rs']).decode()
# The original empty harness was not an input generator. Correct it under the
# SAME name. No passing verdict exists; no verdict is changed by a rename.
suffix=old['suffix'].replace('fn PCA_count_contract() {}', '''fn PCA_count_contract() {
        let accounts: &[AccountInfo<'_>] = kani::any();
        let expected: usize = kani::any();
        let _ = require_exact_account_count(accounts, expected);
    }''')
meta={**old,'suffix':suffix};a=source.index('fn require_exact_account_count');modified=source[:a]+meta['annotation']+source[a:]+suffix
meta['modified_sha256']=hashlib.sha256(modified.encode()).hexdigest();(E/'PCA_NATIVE_PATCH_META.json').write_text(json.dumps(meta,indent=1)+'\n')
(E/'PCA_native_packets.patch').write_text(''.join(difflib.unified_diff(source.splitlines(True),modified.splitlines(True),fromfile='a/programs/aspis-pool/src/pair_forest.rs',tofile='b/programs/aspis-pool/src/pair_forest.rs')))
updates=json.loads((E/'PCA_NATIVE_REPAIR_FILES.json').read_text());updates['PCA_src/programs/aspis-pool/src/pair_forest.rs']=modified;updates['PCA_NATIVE_PATCH_META.json']=(E/'PCA_NATIVE_PATCH_META.json').read_text();(E/'PCA_NATIVE_REPAIR_FILES.json').write_text(json.dumps(updates,indent=1)+'\n')
# Preserve stronger validation while pinning the actual CLI before each stage.
p=E/'PCA_native_gate.py';s=p.read_text();s=s.replace("try:\n status=subprocess.run",'''tools={}
for label,cmd in [('cargo',['/home/dombarker/.cargo/bin/cargo','--version']),('kani',['/home/dombarker/.cargo/bin/cargo-kani','--version'])]:
 q=subprocess.run(cmd,capture_output=True,text=True);assert q.returncode==0
 tools[label]=dict(command=cmd,stdout=q.stdout,stderr=q.stderr,path_sha256=sha(Path(cmd[0]).resolve()))
assert '0.67.0' in tools['kani']['stdout']+tools['kani']['stderr']
(B/(a+'-tool-pins.json')).write_text(json.dumps(tools,indent=1)+'\\n')
try:
 status=subprocess.run''');p.write_text(s);compile(s,str(p),'exec')
print('Retired cold monolithic compile; isolated dependency predecessor and corrected same-named target-call harness prepared.')
