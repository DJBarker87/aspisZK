from pathlib import Path
import re,hashlib,json,shutil
root=Path(__file__).resolve().parent
src=root.parent/'r314-slice-last-translation/generated/AspisR314SliceLast/Funs.lean'
assert hashlib.sha256(src.read_bytes()).hexdigest()=='324668a3095503b19272ad1a569ea7650f889b7cd982d1c4531891d52bbebbd1'
txt=src.read_text(); start=txt.index('/-- [core::slice::{[T]}::last]:');end=txt.index('\nend AspisR314SliceLast',start);block=txt[start:end].rstrip()+'\n'
assert block.count('\ndef ')==1 and 'axiom ' not in block
out='import Aeneas.Std\nopen Aeneas Aeneas.Std Result ControlFlow Error\n\nnamespace AspisR316SliceLastRaw\n\n'+block+'\n#print axioms core.slice.Slice.last\n\nend AspisR316SliceLastRaw\n'
f=root/'AspisR316SliceLastRaw.lean';f.write_text(out)
(root/'provenance').mkdir(exist_ok=True);shutil.copyfile(src,root/'provenance/R314Funs.input.lean')
(root/'binding-audit.json').write_text(json.dumps({'generated_source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'target_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'generated_definition_and_attribute_doc_block_sha256':hashlib.sha256(block.encode()).hexdigest(),'generated_block_unchanged':True,'input_fun_id':12,'signature':'{T:Type} -> Slice T -> Result (Option T)','library_dependencies':['Aeneas.Std.Slice.len','Aeneas.Std.Usize.sub','Aeneas.Std.Slice.index_usize'],'fresh_types_or_execution_assumptions':False,'adaptations':'import/header/namespace only; no generated definition edits','boundary':'Uncompiled exact generated body staging; root compiles and proves separately.'},indent=2)+'\n')
