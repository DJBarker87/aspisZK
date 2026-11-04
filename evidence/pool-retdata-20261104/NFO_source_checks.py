"""Exact cut and invariant source checks, with intentional mutation controls."""
from pathlib import Path
import subprocess,re,json,hashlib,lzma
E=Path(__file__).resolve().parent;REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
get=lambda p:subprocess.check_output(['git','show',REV+':'+p],text=True)
p='programs/aspis-pool/src/pair_forest_dispatch.rs';rust=get(p)
a=rust.index('    runtime.clear_return_data();',rust.index('fn invoke_pair_forest_terminal_with_runtime_v1'));b=rust.index('\n}\n',a)
def expected(s):
 a=s.index('    runtime.clear_return_data();',s.index('fn invoke_pair_forest_terminal_with_runtime_v1'));b=s.index('\n}\n',a)
 return s[a:b].replace('decode_pool_v1_pair_forest_terminal_result_v1(&returned_data)','decode(&returned_data,frame)').replace('plan.selected_verifier','selected')
positive=json.loads((E/'NFO_K007-shape.json').read_text());assert positive['source_cut']==expected(rust)
cut=expected(rust)
checks={
 'unchanged_frozen_source':Path(p).read_text()==rust,
 'exact_cut':cut in positive['source'],
 'ordered_runtime_calls':re.findall(r'runtime\s*\.\s*(\w+)\(',cut)==['clear_return_data','invoke','get_return_data'],
 'program_before_length_before_decode':cut.index('returned_program != selected')<cut.index('returned_data.len()')<cut.index('decode(&returned_data,frame)'),
 'same_typed_reply_to_box':'value: Box::new(result)' in cut,
 'same_owned_bytes_to_box':'exact_bytes: returned_data.into_boxed_slice()' in cut,
 'empty_function_pointer_quarantine':not re.search(r'Option\s*<\s*fn|static\s+mut|static\s+\w+\s*:\s*(?:Cell|RefCell|Atomic)',positive['source']),
 'runtime_wrapper_invoke':'program::invoke(instruction, account_infos)' in rust,
 'runtime_wrapper_read':'program::get_return_data()' in rust,
}
assert all(checks.values()),checks
mutations=[]
for old,new in [('returned_program != plan.selected_verifier','returned_program == plan.selected_verifier'),('runtime.invoke(&instruction, &infos)?;','runtime.invoke(&instruction, &infos)?;\n    runtime.clear_return_data();'),('decode_pool_v1_pair_forest_terminal_result_v1(&returned_data)','decode_pool_v1_pair_forest_terminal_result_v1(&returned_data[1..])'),('value: Box::new(result)','value: Box::new(other)'),('exact_bytes: returned_data.into_boxed_slice()','exact_bytes: other.into_boxed_slice()')]:
 assert old in rust
 mutations.append(dict(original=old,mutated=new,rejected=expected(rust.replace(old,new))!=positive['source_cut']))
assert all(m['rejected'] for m in mutations)
# Pin exact ELF post-CPI sequence. Successful tag branch selects fallthrough.
dis=lzma.decompress((E/'NFO_pool_disassembly.txt.xz').read_bytes()).decode()
ins={int(m[1],16):m[2].strip() for l in dis.splitlines() if (m:=re.match(r'\s*([0-9a-f]+):\s+(?:[0-9a-f]{2}\s+)+\s*\t(.+)',l))}
assert ins[0x3eb0]=='call 0xb74b'
assert ins[0x3ee8]=='call 0xb7b7'
assert not any('call' in ins[x] for x in [0x3eb8,0x3ec0,0x3ed0,0x3ed8,0x3ee0])
assert '0x318' in ins[0x4078]
result=dict(status='PASS',frozen_revision=REV,checks=checks,mutations=mutations,source_sha256=hashlib.sha256(rust.encode()).hexdigest(),scope='source-exact post-admission ASR8 cut; not decoder or settlement correspondence',elf_post_cpi_sequence={hex(x):ins[x] for x in [0x3eb0,0x3eb8,0x3ec0,0x3ed0,0x3ed8,0x3ee0,0x3ee8]})
(E/'NFO_SOURCE_CHECKS.json').write_text(json.dumps(result,indent=1)+'\n');print('PASS source cut, 5 mutations, exact post-CPI ELF sequence')
