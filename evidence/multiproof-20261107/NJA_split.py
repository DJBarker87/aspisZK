from pathlib import Path
import re,json,hashlib
E=Path(__file__).parent;p=E/'NJA_emitted/raw/NHR_NJA_multiproof/Funs.lean';s=p.read_text();names=['LEAF_BITS','BINARY_NODE_TAG','MAX_BATCH','Arity.bits','Arity.width','Arity.levels','index_at','value_at','root_matches','occupied_binary_parent','sibling_binary_parent'];blocks=[];pins=[]
for n in names:
 m=re.search(r'(?:@\[global_simps, irreducible\] )?def multiproof\.'+re.escape(n)+r'\b',s);assert m,n
 end=s.find('\n/--',m.end());block=s[m.start():end];blocks.append(block);pins.append(dict(name=n,start=m.start(),end=end,sha256=hashlib.sha256(block.encode()).hexdigest()))
out='import NJA_Multiproof.Types\nopen Aeneas Aeneas.Std Result ControlFlow Error\nnoncomputable section\nnamespace NJA_Multiproof\n\n'+'\n\n'.join(blocks)+'\nend NJA_Multiproof\n';(E/'NJA_lean/NJA_Small.lean').write_text(out);(E/'NJA_SPLIT.json').write_text(json.dumps(dict(raw_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),blocks=pins,transformation='contiguous declaration byte slices only; no body edits'),indent=2)+'\n')
print('NJA split: 11 unchanged emitted declaration bodies; unrelated iterator ABI failures isolated')
