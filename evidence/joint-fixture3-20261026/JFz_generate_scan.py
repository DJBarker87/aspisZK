"""Generate word proofs and symbolic joins for retained real-byte ranges."""
from pathlib import Path
import json,hashlib,argparse
R=Path(__file__).resolve().parents[2];p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');a=p.parse_args()
b=(R/'docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures/transfer-13/r1-s2-proof.bin').read_bytes()
assert hashlib.sha256(b).hexdigest()=='55386c507d3feeebfc45272a1cf15c33ccb9ccf0a8a8f41180fc654d806fff6f'
regions=[(7031,464),(7495,256),(7783,2272)]+[(10055+j*832+o,n) for j in range(22) for o,n in [(0,608),(672,128)]]
rowoff=48
for row in range(27):
 size=32 if row in (2,14) else 896 if 15<=row<=24 else 3712 if row==25 else 928 if row==26 else 0
 n=size//2 if row>=14 else size
 if row>=14:regions.append((rowoff+5,n))
 rowoff+=5+n
assert rowoff==7031
# Simplify list geometry using named lengths; unfold at most two literal leaves.
def select_proof(off,n):
 common=['List.drop_append','List.take_append','List.length_append','Nat.reduceAdd','Nat.reduceSub','Nat.reduceLeDiff','List.length_drop','List.drop_eq_nil_of_le','List.take_of_length_le','List.drop_zero','List.take_zero','List.nil_append','List.append_nil']
 out=['  change (JFx_NativeBytes.proofBytes.drop _).take _ = _','  simp only ['+','.join(['JFx_NativeBytes.proofBytes']+[f'JFx_DataProof{z:02d}.length' for z in range(15)]+common)+']']
 pieces=[]
 for part in range(off//4096,(off+n-1)//4096+1):
  pref=f'JFx_DataProof{part:02d}';pieces += [pref+'.bytes']+[pref+f'.c{k:02d}_length' for k in range((min(4096,len(b)-part*4096)+31)//32)]
 out+=['  simp only ['+','.join(pieces+common)+']','  rfl']
 return out
manifest=[]
for i,(off,n) in enumerate(regions):
 mod=f'JFz_Scan{i:02d}';raw=b[off:off+n];assert n%4==0 and all(int.from_bytes(raw[j:j+4],'little')<2147483647 for j in range(0,n,4))
 lines=['import JFz_CanonicalAppend','import JFx_NativeBytes','set_option autoImplicit false','noncomputable section',f'namespace AspisR1.{mod}','open Aeneas Aeneas.Std','open AspisV8R19.DuplexFrames OraclePortCompactDraft MultiproofConeCanonical']
 if i>0:lines.insert(3,'set_option linter.unusedSimpArgs false')
 leaves=[]
 for k,start in enumerate(range(0,n,32)):
  r=raw[start:start+32];q=f'b{k:02d}';leaves.append((q,off+start,len(r)))
  lines += [f'def {q} : List U8 := ['+','.join(f'{v}#u8' for v in r)+']',f'theorem {q}_length : {q}.length = {len(r)} := by simp only [{q},List.length_cons,List.length_nil]',f'theorem {q}_canonical : canonical (bytesOf {q}) := by',f'  change canonical ['+','.join(str(v) for v in r)+']','  simp only [canonical_four]','  exact '+('⟨by decide, '*(len(r)//4))+'JFz_Canonical.nil'+('⟩'*(len(r)//4)),f'theorem {q}_selected : (JFx_NativeBytes.proof.val.drop {off+start}).take {len(r)} = {q} := by']+select_proof(off+start,len(r))
  for t in ['length','canonical','selected']:lines.append(f'#print axioms {q}_{t}')
 counter=[0]
 def join(xs):
  if len(xs)==1:return xs[0]
  k=len(xs)//2;l,lo,ln=join(xs[:k]);r,ro,rn=join(xs[k:]);q=f'j{counter[0]:02d}';counter[0]+=1;assert lo+ln==ro
  lines.extend([f'def {q} : List U8 := {l} ++ {r}',f'theorem {q}_length : {q}.length = {ln+rn} := by rw [{q},List.length_append,{l}_length,{r}_length]',f'theorem {q}_canonical : canonical (bytesOf {q}) := JFz_CanonicalAppend.join _ _ {l}_canonical {r}_canonical',f'theorem {q}_selected : (JFx_NativeBytes.proof.val.drop {lo}).take {ln+rn} = {q} := by',f'  rw [JFz_CanonicalAppend.slice_join _ {lo} {ln} {rn},{l}_selected,{r}_selected]', '  rfl'])
  for t in ['length','canonical','selected']:lines.append(f'#print axioms {q}_{t}')
  return q,lo,ln+rn
 q,_,_=join(leaves)
 lines += [f'def data : List U8 := {q}',f'theorem length : data.length = {n} := {q}_length',f'theorem canonical_data : canonical (bytesOf data) := {q}_canonical',f'theorem selected : (JFx_NativeBytes.proof.val.drop {off}).take {n} = data := {q}_selected',f'theorem canonical_selected : canonical (slice (bytesOf JFx_NativeBytes.proof.val) {off} {n}) := by','  simp only [slice,bytesOf, ← List.map_drop, ← List.map_take,selected]','  exact canonical_data']
 for t in ['length','canonical_data','selected','canonical_selected']:lines.append(f'#print axioms {t}')
 lines += [f'end AspisR1.{mod}','end']
 text='\n'.join(lines)+'\n';target=R/'lean'/f'{mod}.lean'
 if a.check:assert target.read_text()==text
 else:target.write_text(text)
 manifest.append({'module':mod,'offset':off,'bytes':n,'data_sha256':hashlib.sha256(raw).hexdigest(),'source_sha256':hashlib.sha256(text.encode()).hexdigest()})
out=R/'evidence/joint-fixture3-20261026/JFz_SCAN_MANIFEST.json'
if a.check:assert json.loads(out.read_text())==manifest
else:out.write_text(json.dumps(manifest,indent=2)+'\n')
