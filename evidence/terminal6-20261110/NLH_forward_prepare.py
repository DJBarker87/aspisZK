from pathlib import Path
import subprocess,hashlib,json,re,difflib
p=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387';name='crates/aspis-statement/src/pool_v1/pair_forest_semantic_terminal.rs'
s=subprocess.check_output(['git','show',rev+':'+name],text=True)
def body(s,n):
 i=s.index('fn '+n+'(');i=s.index('{',i);j=i+1;d=1
 while d:d+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[i+1:j-1]
compact=lambda x:re.sub(r'\s+','',x)
b=body(s,'terminal_qm31');prefix='let selected = core::array::from_fn(|i| claims[i / 28][i % 28]);'
assert compact(b).startswith(compact(prefix))
tail=b[b.index('terminal_parts('):]
translated=tail.replace('terminal_parts(','NLH_parts_oracle(').replace('self.semantic()','public').replace('&selected','selected').replace('c.mu,','c.mu,l,').replace('Error::Public','PrefixError::Public')
# Extra source argument l may be formatted without a trailing comma.
translated=translated.replace('c.mu,l,','c.mu,l')
actual=body((p/'NLH_Forward_native.rs.txt').read_text(),'NLH_terminal_forward')
assert compact(translated)==compact(actual),(translated,actual)
old=s
mods={'TermSemantic':'NKR_term_semantic_native','TermScalarWindows':'NKR_scalar_windows_native','TermPrefix':'NKR_prefix_native','TermHorner':'NKR_horner_native'}
for f,m in mods.items():old+='\n#[cfg(kani)]\n#[path="NLH_'+f+'_native.rs"]\nmod '+m+';\n'
new=old+'\n#[cfg(kani)]\n#[path="NLH_Forward_native.rs"]\nmod NLH_forward_native;\n'
code=(p/'NLH_Forward_native.rs.txt').read_text()
patch=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+name,tofile='b/'+name))
file='crates/aspis-statement/src/pool_v1/NLH_Forward_native.rs'
patch+=''.join(difflib.unified_diff([],code.splitlines(True),fromfile='/dev/null',tofile='b/'+file))
(p/'NLH_forward.patch').write_text(patch)
pins=json.loads((p/'NLH_SOURCE_PINS.json').read_text());pins[name]=hashlib.sha256(new.encode()).hexdigest();pins[file]=hashlib.sha256(code.encode()).hexdigest();(p/'NLH_SOURCE_PINS.json').write_text(json.dumps(pins,indent=2)+'\n')
(p/'NLH_FORWARD_TRANSCRIPTION.json').write_text(json.dumps(dict(revision=rev,frozen_source=name,frozen_sha256=hashlib.sha256(s.encode()).hexdigest(),frozen_body=b,native_tail=actual,translation=translated,identity=True,scope='SAME256 tail after gather and CLOSED255; full263 Rust Result including both Err variants, exact arguments, readonly frames and returned scalar. Not whole-parent credit by itself.',harness_sha256=hashlib.sha256(code.encode()).hexdigest()),indent=2)+'\n')
print('256 frozen forwarding expression and Result maps match')
