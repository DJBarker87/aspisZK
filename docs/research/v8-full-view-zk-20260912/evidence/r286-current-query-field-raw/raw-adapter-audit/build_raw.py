from pathlib import Path
import argparse, hashlib, re, json, difflib
parser=argparse.ArgumentParser()
parser.add_argument('--audit-only',action='store_true',help='verify and refresh audits without rewriting the Lean target')
args=parser.parse_args()
repo=Path(__file__).resolve().parents[2]
src=repo/'.r21-scratch/r291-query-field-leaf-translation/generated/AspisAspisR291QueryFieldLeaves/Funs.lean'
src_types=repo/'.r21-scratch/r291-query-field-leaf-translation/generated/AspisAspisR291QueryFieldLeaves/Types.lean'
r156f=repo/'docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/FunsCore.lean'
r156t=repo/'docs/research/v8-full-view-zk-20260912/lean/AspisR156FullFreeze/Types.lean'
r239=repo/'docs/research/v8-full-view-zk-20260912/lean/AspisR239CoeffExecutionRaw.lean'
outdir=repo/'.r21-scratch/r286-query-field-raw'; outdir.mkdir(parents=True,exist_ok=True)
EXPECTED='b6ae3414ca592fb438974a45a49ea62ed98be80d8a81e5d61442a6209247621c'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(src)==EXPECTED, sha(src)
def block(text, qname):
    # Include exact docstring/attributes/definition through line before next docstring/end namespace.
    marker='def '+qname
    at=text.index(marker)
    start=text.rfind('/--',0,at)
    if start<0: raise ValueError(qname)
    # Include beginning of doc comment, exclude preceding blank lines.
    nxt=re.search(r'(?m)^/--|^end Aspis',text[at+len(marker):])
    end=at+len(marker)+(nxt.start() if nxt else len(text[at+len(marker):]))
    # trim trailing whitespace only; preserve internal text exactly
    return text[start:end].rstrip()
roots=['aspis_core.field.QM31.neg','aspis_core.field.QM31.mul_m31']
blocks={n:block(src.read_text(),n) for n in roots}
# The extraction point at the docstring ensures source blocks are byte-for-byte substrings.
for n,b in blocks.items(): assert b in src.read_text()
header='''import Aeneas.Std\nimport AspisR156FullFreeze.FunsCore\nimport AspisR239CoeffExecutionRaw\n\nopen Aeneas Aeneas.Std Result\nopen AspisR156FullFreeze AspisR239CoeffExecutionRaw\nset_option linter.dupNamespace false\nset_option linter.hashCommand false\nset_option autoImplicit false\n\nnamespace AspisR286QueryFieldRaw\n\n'''
trailer='''\n\n#print axioms aspis_core.field.QM31.neg\n#print axioms aspis_core.field.QM31.mul_m31\n\nend AspisR286QueryFieldRaw\n'''
dest=outdir/'AspisR286QueryFieldRaw.lean'
promoted=repo/'docs/research/v8-full-view-zk-20260912/lean/AspisR286QueryFieldRaw.lean'
generated=header+'\n\n'.join(blocks[n] for n in roots)+trailer
if args.audit_only:
    raw_existing=dest.read_text()
    assert raw_existing.startswith('import Aeneas.Std\n')
    assert all(b in raw_existing for b in blocks.values())
else:
    dest.write_text(generated)
assert promoted.exists() and sha(promoted)==sha(dest), 'promoted/staged raw file mismatch'
# Verify selected source blocks copied verbatim in order, ignoring wrapper lines.
raw=dest.read_text()
assert raw.index(blocks[roots[0]]) < raw.index(blocks[roots[1]])
# Exact helper definitions, with the sole authorized literal adaptation in M31.mul.
gen=src.read_text(); core=r156f.read_text(); coeff=r239.read_text()
checks=[
 ('P','aspis_core.field.P',core,None),
 ('M31.neg','aspis_core.field.M31.neg',core,None),
 ('CM31.neg','aspis_core.field.CM31.neg',core,None),
 ('reduce_u64','aspis_core.field.reduce_u64',core,None),
 ('M31.mul','aspis_core.field.M31.mul',core,'count31_i32_to_u32'),
 ('CM31.mul_m31','aspis_core.field.CM31.mul_m31',coeff,None),
]
# Compare declaration bodies from first `def` through its next docstring / namespace end.
def body(text,qname):
    i=text.index('def '+qname)
    # balance by taking to the next top-level doc comment/end marker
    m=re.search(r'(?m)^/--|^def |^abbrev |^end ',text[i+1:])
    s=text[i:i+1+m.start()] if m else text[i:]
    return s.strip()
helper_report=[]
for label,qname,reftext,adapter in checks:
    g=body(gen,qname)
    ref=body(reftext,qname)
    if adapter:
        assert g.count('31#i32')==1, (label,g.count('31#i32'))
        gnorm=g.replace('31#i32','31#u32')
    else: gnorm=g
    equal=gnorm==ref
    if not equal:
        # Display for debugging and fail closed.
        print(label,'MISMATCH')
        print('\n'.join(difflib.unified_diff(ref.splitlines(),gnorm.splitlines(),fromfile='reference',tofile='generated')))
    assert equal, label
    helper_report.append({'helper':label,'generated_definition_sha256':hashlib.sha256(g.encode()).hexdigest(),'bound_to':('AspisR239CoeffExecutionRaw' if label=='CM31.mul_m31' else 'AspisR156FullFreeze'),'body_equal_after_authorized_adapter':True,'authorized_adapter':adapter or 'none'})
# Type-layout/source binding inspection: canonical three type declarations.
def decl_signature(text,name):
    i=text.index('def aspis_core.field.'+name) if name=='M31' else text.index('structure aspis_core.field.'+name)
    if name=='M31':
        return re.search(r'def aspis_core\.field\.M31\s*:=\s*([^\n]+)',text[i:]).group(1).strip()
    m=re.search(r'structure aspis_core\.field\.'+name+r' where\n((?:  [^\n]+\n)+)',text[i:])
    return [ln.strip() for ln in m.group(1).splitlines() if ln.strip()]
type_report=[]
for name in ('M31','CM31','QM31'):
    gt=decl_signature(src_types.read_text(),name); rt=decl_signature(r156t.read_text(),name)
    assert gt==rt,(name,gt,rt)
    type_report.append({'type':name,'layout':gt,'matches_R156':True})
report={'source_sha256':sha(src),'source_types_sha256':sha(src_types),'R156_FunsCore_sha256':sha(r156f),'R156_Types_sha256':sha(r156t),'R239_raw_sha256':sha(r239),'raw_target_sha256':sha(dest),'promoted_raw_target_sha256':sha(promoted),'builder_sha256':sha(Path(__file__)),'selected_blocks':[{'name':n,'body_sha256':hashlib.sha256(blocks[n].encode()).hexdigest(),'verbatim_copy':True} for n in roots],'helper_bindings':helper_report,'type_layouts':type_report,'root_declarations':roots,'raw_print_axioms_count':2,'source_body_replacements':0,'translation_or_compile_run':False,'scope':'Raw selected root staging and mechanical binding audit only; no source correspondence, theorem, or release conclusion.'}
(outdir/'binding-audit.json').write_text(json.dumps(report,indent=2)+'\n')
(outdir/'root-comparison.json').write_text(json.dumps({'input':str(src.relative_to(repo)),'input_sha256':sha(src),'selected_blocks':[{'name':n,'copied_exactly':blocks[n] in raw,'sha256':hashlib.sha256(blocks[n].encode()).hexdigest()} for n in roots],'output_sha256':sha(dest)},indent=2)+'\n')
print(json.dumps({'output':str(dest),'hash':sha(dest),'helpers':len(helper_report),'types':len(type_report)},indent=2))

# Full reproducibility checksum list for the exact inputs and generated artifacts.
checksum_paths=[src,src_types,r156f,r156t,r239,dest,promoted,Path(__file__),outdir/'README.md',outdir/'binding-audit.json',outdir/'root-comparison.json',outdir/'rejected-import-scaffold/AspisR286QueryFieldRaw.failed-import-Aeneas.lean',outdir/'rejected-import-scaffold/rejection.json',outdir/'rejected-import-scaffold/binding-audit.pre-import-fix.json',outdir/'rejected-import-scaffold/root-comparison.pre-import-fix.json']
(outdir/'checksums.sha256').write_text(''.join(f"{sha(p)}  {p.relative_to(repo)}\n" for p in checksum_paths))
