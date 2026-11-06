from pathlib import Path
import subprocess,re,json,hashlib
E=Path(__file__).resolve().parent
rev='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
p='programs/aspis-verifier/src/v7_pair_empty_roots.rs'
raw=subprocess.check_output(['git','show',rev+':'+p]);s=raw.decode();section=s[s.index('pub const V7_PAIR_EMPTY_ROOTS'):];section=section[:section.index('\n];')]
words=[int(x) for x in re.findall(r'M31\((\d+)\)',section)];assert len(words)==168 and all(0<=x<2147483647 for x in words)
t='import NKP_LaneCarrier\nset_option autoImplicit false\nnamespace NLK_LaneTable\nopen Aeneas Aeneas.Std\n'
t+='def values : Array (Array U32 8#usize) 21#usize := ⟨[\n'
for i in range(21):t+=' ⟨['+','.join(str(x)+'#u32' for x in words[i*8:(i+1)*8])+'],by decide⟩'+(',' if i<20 else '')+'\n'
t+='],by decide⟩\n'
t+='''def node (i : Fin 21) : NKP_LaneCuts.Node := fun j =>
 (values.val[i.val]'(by simpa [values.property] using i.isLt)).val[j.val]'(by
   have h := (values.val[i.val]'(by simpa [values.property] using i.isLt)).property
   simpa [h] using j.isLt)
def empty (i : Fin 20) : NKP_LaneCuts.Node := node ⟨i.val,by omega⟩
def final : NKP_LaneCuts.Node := node ⟨20,by decide⟩
theorem count : values.val.length=21 := values.property
#print axioms count
end NLK_LaneTable
'''
(E/'NLK_LaneTable.lean').write_text(t)
(E/'NLK_TABLE_PIN.json').write_text(json.dumps(dict(source=p,revision=rev,sha256=hashlib.sha256(raw).hexdigest(),words=168,meaning='literal frozen table; no Poseidon evaluation or new value premise'),indent=1)+'\n')
