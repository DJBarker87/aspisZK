#!/usr/bin/env python3
"""Pin final LLBC, emitted files, concrete cone declarations, tools and inputs."""
from pathlib import Path
import hashlib,json,sys
H=Path('/home/dombarker/project-offloads/codex-cx-stage2b-20261020');attempt=sys.argv[1];tag=sys.argv[2];D=H/('extraction-'+attempt);O=H/('publication-'+tag);O.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
p=D/'Stage2.llbc';llbc=json.loads(p.read_text());assert llbc['has_errors'] is False
rows=[]
for f in llbc['translated']['fun_decls']:
 if f is None:continue
 parts=[q['Ident'][0] if 'Ident' in q else '{impl}' for q in f['item_meta']['name']];name='::'.join(parts)
 if parts and parts[0]=='aspis_r1_cost_probe':rows.append(dict(name=name,body_kind=list(f['body'])[0] if isinstance(f['body'],dict) else f['body'],source_span=f['item_meta']['span']))
required=['tx2_authenticated','tx2_common','resume','parse_shape','query_loop','query_values','accumulate_batched_with_node','finish_relation','finish_query_dot','batch_tree','node_count','verify_in_place','polynomial']
for name in required:
 matches=[r for r in rows if r['name'].split('::')[-1]==name];assert matches and all(r['body_kind']=='Structured' for r in matches),name
files=[dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size,committed=p.name in ['Funs.lean','Types.lean']) for p in sorted((D/'generated').rglob('*')) if p.is_file()]
inputs=json.loads((H/'pins/build-inputs.json').read_text())
for f in inputs['files']:assert sha(H/'src'/f['path'])==f['sha256'],f['path']
lowering=json.loads((D/'aeneas-input.json').read_text())
for path,expected in lowering['source_hashes'].items():assert sha(H/'src'/path)==expected,path
runtime=json.loads((H/'pins/runtime-inputs.json').read_text())
for f in runtime:assert sha(Path(f['path']))==f['sha256'],f['path']
tools=[]
for p in [Path('/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf'),Path('/home/dombarker/.cache/solana/v1.52/platform-tools/rust/bin/rustc'),Path('/home/dombarker/.cache/solana/v1.52/platform-tools/rust/lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld'),H/('harness-'+tag)/'sbf-linker/rust-lld',H/'native-target/release/examples/r1p_retry_gate']:
 assert p.is_file(),p
 tools.append(dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size))
result=dict(source_revision=inputs['base_revision'],attempt=attempt,extraction_input_declared_revision=lowering['source_revision'],extraction_source_hashes_match_final_revision=True,llbc=dict(path=str(D/'Stage2.llbc'),sha256=sha(D/'Stage2.llbc'),bytes=(D/'Stage2.llbc').stat().st_size,has_errors=False),generated_files=files,required_concrete_functions=required,local_functions=rows,tools=tools,build_inputs_verified=len(inputs['files']),runtime_inputs_verified=len(runtime),runtime_inputs=runtime,classification='Successful whole-cone Aeneas emission with explicit backend frontiers; raw external templates are pinned but not accepted proofs.')
(O/'extraction-pins.json').write_text(json.dumps(result,indent=2)+'\n')
print('verified concrete cone and pins',len(rows),len(files),len(inputs['files']),len(runtime))
