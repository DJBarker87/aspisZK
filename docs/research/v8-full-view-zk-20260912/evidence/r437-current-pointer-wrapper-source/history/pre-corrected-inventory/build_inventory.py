#!/usr/bin/env python3
"""Repackage already-saved R430 pinned-source copies and exact cited excerpts."""
import hashlib,json,shutil
from pathlib import Path
W=Path('/Users/dominic/ZK/.worktrees/ZK-v8-r21-public-arithmetic-20260922')
R=W/'.r21-scratch/r430-actual-fold-primitive-boundary'
O=W/'.r21-scratch/r437-pointer-source-boundary/inventory'
A=R/'size-global-inventory/source'
L=R/'pointer-api-inventory/source/Aeneas/Std'
files={
 'aeneas/Expressions.ml':A/'Expressions.ml',
 'aeneas/ExpressionsUtils.ml':A/'ExpressionsUtils.ml',
 'aeneas/FunsAnalysis.ml':A/'FunsAnalysis.ml',
 'aeneas/InterpExpressions.ml':A/'InterpExpressions.ml',
 'aeneas/InterpPaths.ml':A/'InterpPaths.ml',
 'aeneas/InterpStatements.ml':A/'InterpStatements.ml',
 'aeneas/InterpUtils.ml':A/'InterpUtils.ml',
 'aeneas/PrePasses.ml':A/'PrePasses.ml',
 'lean/Aeneas/Std/RawPtr.lean':L/'RawPtr.lean',
 'lean/Aeneas/Std/Core/Ptr.lean':L/'Core/Ptr.lean',
 'lean/Aeneas/Std/Slice.lean':L/'Slice.lean',
}
for rel,src in files.items():
 dst=O/'source'/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
extra_sources={
 'charon/ast/types.rs':('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/src/ast/types.rs','src/ast/types.rs'),
 'charon/bin/charon-driver/translate/translate_types.rs':('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/src/bin/charon-driver/translate/translate_types.rs','src/bin/charon-driver/translate/translate_types.rs'),
 'charon/bin/charon-driver/hax/types/ty.rs':('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon/src/bin/charon-driver/hax/types/ty.rs','src/bin/charon-driver/hax/types/ty.rs'),
 'aeneas/llbc/Types.ml':('/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a/src/llbc/Types.ml','src/llbc/Types.ml'),
 'aeneas/symbolic/SymbolicToPureTypes.ml':('/home/dombarker/project-offloads/aspis-r425-unit-constant-candidate-20261002-a/src/symbolic/SymbolicToPureTypes.ml','src/symbolic/SymbolicToPureTypes.ml'),
}
prior={
 'prior-r430/pointer-api-README.md':R/'pointer-api-inventory/README.md',
 'prior-r430/pointer-api-search.txt':R/'pointer-api-inventory/aeneas-pointer-api-search.txt',
 'prior-r430/pointer-api-search.status':R/'pointer-api-inventory/aeneas-pointer-api-search.status',
 'prior-r430/pointer-api-inventory.json':R/'pointer-api-inventory/inventory.json',
 'prior-r430/size-global-inventory.json':R/'size-global-inventory/inventory.json',
}
for rel,src in prior.items():
 dst=O/rel;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(src,dst)
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
pi=json.loads((R/'pointer-api-inventory/inventory.json').read_text())
sgi=json.loads((R/'size-global-inventory/inventory.json').read_text())
def excerpt(rel,ranges):
 p=O/'source'/rel; lines=p.read_text().splitlines()
 out=[]
 for lo,hi,label in ranges:
  out.append(f'\n### {rel}:{lo}-{hi} — {label}\n')
  out.extend(f'{n:5d} {lines[n-1]}\n' for n in range(lo,min(hi,len(lines))+1))
 return ''.join(out)
sections=[]
sections.append(excerpt('aeneas/InterpExpressions.ml',[(216,246,'Copying borrow content'),(1070,1139,'Concrete binary operation evaluation'),(1141,1200,'Symbolic binary operation classification'),(1222,1303,'Reference creation'),(1377,1389,'Aggregate raw pointer case'),(1492,1510,'Rvalue dispatch and unsupported fallback')]))
sections.append(excerpt('aeneas/InterpPaths.ml',[(108,122,'Raw-pointer dereference rejection'),(137,205,'Borrow projection and mutable-borrow path'),(265,283,'Place projection/global access boundary')]))
sections.append(excerpt('aeneas/InterpStatements.ml',[(420,475,'Call argument evaluation, frame push/pop, builtin dispatch'),(908,930,'Assignment/global dispatch'),(1021,1053,'Shared global reference handling')]))
sections.append(excerpt('aeneas/InterpUtils.ml',[(440,456,'Rvalue place extraction')]))
sections.append(excerpt('aeneas/ExpressionsUtils.ml',[(1,30,'Global access detector')]))
sections.append(excerpt('aeneas/PrePasses.ml',[(115,160,'Raw slice-pointer metadata candidate recognition'),(2835,2916,'Global access decomposition')]))
sections.append(excerpt('lean/Aeneas/Std/RawPtr.lean',[(1,33,'RawPtr type and scalar cast')]))
sections.append(excerpt('lean/Aeneas/Std/Core/Ptr.lean',[(74,88,'Layout and GlobalAlloc declarations')]))
sections.append(excerpt('lean/Aeneas/Std/Slice.lean',[(23,54,'List-facing Slice operations and length'),(337,368,'SliceIndex and get_unchecked sorry'),(397,407,'Unchecked range index fails undef'),(538,590,'Unchecked usize index fails undef and specification sorry')]))
# New, explicitly requested pattern-schema check fetched read-only from the same pinned trees.
for rel,ranges in [
 ('charon/ast/types.rs',[(1092,1105,'Charon TyKind includes Pattern(Ty,TypePattern)'),(1280,1301,'TypePattern constructors, including NotNull')]),
 ('charon/bin/charon-driver/hax/types/ty.rs',[(750,763,'Hax TyKind Pat source variant'),(905,920,'Hax Pattern enum and conversion')]),
 ('charon/bin/charon-driver/translate/translate_types.rs',[(175,190,'Charon TyKind Pattern construction'),(319,337,'Hax Pattern to TypePattern mapping')]),
 ('aeneas/llbc/Types.ml',[(1,13,'Aeneas LLBC.Types directly includes Charon.Types')]),
 ('aeneas/symbolic/SymbolicToPureTypes.ml',[(155,216,'Aeneas pure-type translation cases and unsupported fallback')]),
]: sections.append(excerpt(rel,ranges))
(O/'source-excerpts.txt').write_text('\n'.join(sections))
files_index={}
for rel,src in files.items():
 dst=O/'source'/rel
 upstream = {
  'aeneas/Expressions.ml':'llbc/Expressions.ml',
  'aeneas/ExpressionsUtils.ml':'llbc/ExpressionsUtils.ml',
  'aeneas/FunsAnalysis.ml':'llbc/FunsAnalysis.ml',
  'aeneas/InterpExpressions.ml':'interp/InterpExpressions.ml',
  'aeneas/InterpPaths.ml':'interp/InterpPaths.ml',
  'aeneas/InterpStatements.ml':'interp/InterpStatements.ml',
  'aeneas/InterpUtils.ml':'interp/InterpUtils.ml',
  'aeneas/PrePasses.ml':'PrePasses.ml',
}.get(rel)
 pinned_root = pi['pins']['aeneas_candidate']['path'] if rel.startswith('aeneas/') else pi['pins']['aeneas_lean_library']['path']
 pinned_path = str(Path(pinned_root)/(upstream if upstream else rel.removeprefix('lean/')))
 files_index[rel]={'saved_from_r430':str(src.relative_to(W)),'pinned_source_path':pinned_path,'sha256':digest(dst),'size_bytes':dst.stat().st_size}
for rel,(remote_path,short) in extra_sources.items():
 dst=O/'source'/rel
 root = pi['pins']['aeneas_candidate']['path'] if rel.startswith('aeneas/') else '/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon/charon'
 files_index[rel]={'saved_from_r430':None,'read_only_fetch':'NUC SSH, no source mutation','pinned_source_path':remote_path,'pinned_tree':root,'sha256':digest(dst),'size_bytes':dst.stat().st_size}

# Source-root identity comes from the already-saved R430 inventories.
inv={
 'title':'R437 pinned Aeneas raw-pointer, offset, globals, and borrow/frame source inventory',
 'scope':'Read-only reuse of the R430 saved sources/API inventories plus five exact files fetched read-only from the same pinned R425 Aeneas/Charon paths for the Pattern/NotNull check. No source/repository/backend changes, builds, translations, theorem or security conclusions.',
 'pinned_roots':{'aeneas_candidate':pi['pins']['aeneas_candidate'],'aeneas_lean_library':pi['pins']['aeneas_lean_library'],'charon_source':{'path':sgi['charon_source_root'],'git_commit':'cb50ff16b9f1066b8a97dc06da704de2da2fa41c','tree_status':'read-only status reported no tracked modifications'}},
 'source_files':files_index,
 'source_revision_caveat':'R430 size/global inventory records no Aeneas git revision. The separate R430 pointer inventory records candidate commit ee7ba72da456d5f353bca9f6739b23750a5dfffa, but the remote R425 source-copy path is not itself a git repository; these five supplemental sources are pinned by absolute path plus exact bytes/hash, and no Aeneas source commit is inferred.',
 'prior_r430_files':{k:{'sha256':digest(O/k),'size_bytes':(O/k).stat().st_size,'source_path':str(v.relative_to(W))} for k,v in prior.items()},
 'support_status':[
  {'topic':'RawPtr creation/rvalue','status':'No general RawPtr value construction case in InterpExpressions.eval_rvalue_not_global dispatch (1498-1510); AggregatedRawPtr explicitly raises unsupported at 1387-1388. Ordinary RvRef creates Rust references (1222-1303), not raw pointers. Lean RawPtr is a wrapper field and cast_scalar returns fail undef (RawPtr.lean:8-31).'},
  {'topic':'Raw-pointer Deref','status':'Explicitly rejected by InterpPaths at 110-116. Lean unchecked slice pointer APIs return fail undef, and Slice.get_unchecked/theorem include sorry markers; exact source lines in excerpts.'},
  {'topic':'Offset and AddChecked','status':'Concrete scalar evaluator supports selected panic arithmetic but not AddChecked/Offset; unmatched cases reach Unimplemented binary operation (InterpExpressions.ml:1078-1138). Symbolic binop typing explicitly rejects AddChecked/SubChecked/MulChecked/Offset at 1193-1194. The copied expression evaluator has no dedicated `Offset` computation case; this finding is based on the cited match branches, not the older R430 negative search receipt.'},
  {'topic':'Read-only globals','status':'The global rvalue path accepts only shared reference to PlaceGlobal (InterpStatements.ml:1021-1031), asserts shared kind, leaves ConcreteMode unimplemented, and in SymbolicMode creates a fresh symbolic value/shared loan (1033-1053). PrePasses.decompose_global_accesses lowers global place reads to a shared reference plus dereference (PrePasses.ml:2835-2916).'},
  {'topic':'Ordinary borrow/frame handling','status':'The interpreter has ordinary shared/mutable borrow and loan paths: eval_rvalue_ref at InterpExpressions.ml:1222-1303, copy_value rejects mutable borrow copying at 223-236, and InterpPaths handles VMutBorrow when access permits at 188-199. Calls evaluate args, push a frame, initialize return/input locals, dispatch builtin bodies, then pop/assign at InterpStatements.ml:431-475. PtrFromParts is in an explicit Unimplemented builtin arm at 464-470. This inventory does not establish a raw-pointer frame/borrow model.'},
  {'topic':'Typed pointer/slice backend abstraction','status':'RawPtr Lean wrapper itself has only a value field; cast_scalar fails undef. Core.Ptr source declares Alignment/Layout and GlobalAlloc signatures (alloc/dealloc return raw pointers), but no raw-pointer arithmetic implementation. Charon TRawPtr types are explicitly mapped by Aeneas translate_sty to its builtin RawPtr type (SymbolicToPureTypes.ml:194-202); this records a type mapping only. Slice is list-facing (`val`, length, indexing and slicing); unchecked pointer indexing/range methods fail undef, and Slice.get_unchecked plus its proof contain sorry. These are literal source facts, not adequacy claims.'},
  {'topic':'Pattern/NotNull type schema','status':'Pinned Charon AST defines TyKind::Pattern(Ty,TypePattern); TypePattern has Range, OrPattern, NotNull. Hax Pattern includes NotNull and Charon translate_types maps hax::TyKind::Pat and hax::Pattern::NotNull into that AST. Aeneas llbc/Types.ml is `include Charon.Types`, so this schema is present in its imported type AST. Aeneas SymbolicToPureTypes.translate_sty enumerates supported type constructors but has no Pattern case in the copied lines 157-215; Pattern therefore reaches the wildcard unsupported-type error in this version. This is a source-level support inventory only; it does not infer R437 capture validity or propose erasing the pattern.'}
 ],
 'line_excerpt_file':'source-excerpts.txt',
 'r430_pointer_inventory_sha256':hashlib.sha256((R/'pointer-api-inventory/inventory.json').read_bytes()).hexdigest(),
 'r430_size_global_inventory_sha256':hashlib.sha256((R/'size-global-inventory/inventory.json').read_bytes()).hexdigest(),
 'caveat':'The copied sources are the exact R430 saved copies except the five explicitly requested Pattern/NotNull sources fetched read-only from the same pinned paths. The old R430 pointer-api-search receipt reports no matches, but these directly inspected saved ML files contain RawPtr occurrences; that earlier negative search receipt is inconsistent and is not used as a completeness claim. The R430 size/global inventory did not independently record an Aeneas source revision; exact source paths and file hashes are retained. No pointer provenance, memory safety, operation semantics, or selected-program correspondence is asserted. The Slice definition itself comes from imported SliceDef, which was not among the saved R430 source copies; this inventory reports only the visible Slice API and its use of `.val`.'
}
(O/'inventory.json').write_text(json.dumps(inv,indent=2,sort_keys=True)+'\n')
readme='''# R437 pinned Aeneas pointer-source boundary\n\nRead-only source inventory, reusing saved R430 source copies and inventories. Exact copied file hashes and byte counts are in `inventory.json`; selected numbered code excerpts are in `source-excerpts.txt`. `source/` contains byte-identical copies of the inspected R430 files plus five exact read-only copies fetched for the requested Pattern/NotNull schema check. Their paths and hashes are listed in the inventory.\n\nThe pinned Lean library has a list-facing `Slice` model, while its `RawPtr` is a small wrapper whose scalar cast returns `fail .undef`. The interpreter source explicitly rejects raw-pointer dereference, does not dispatch raw pointer rvalues to a supported evaluator, reports aggregate raw pointers unsupported, and rejects `AddChecked` and `Offset` in the symbolic binop path. Its generic concrete scalar branch also has no implementation for these operations and falls through to an unimplemented-operation failure. Unchecked slice-pointer APIs return `fail .undef`; the generic `Slice.get_unchecked` definition and an associated spec contain `sorry`.\n\nOrdinary Rust references, shared/mutable borrow bookkeeping, function-frame handling, and a restricted symbolic shared-global path do exist in these sources. The global path is not a raw-pointer model, and this inventory does not infer a usable pointer, frame, alias, or source-correspondence contract.\n\nNo builds, translations, proof checks, or semantic decisions were made.\n'''
(O/'README.md').write_text(readme)
print(json.dumps({'files':len(files_index),'excerpts_bytes':(O/'source-excerpts.txt').stat().st_size,'rawptr_sha':files_index['lean/Aeneas/Std/RawPtr.lean']['sha256']},indent=2))
