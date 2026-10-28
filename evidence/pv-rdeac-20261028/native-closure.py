from pathlib import Path
import json,lzma,subprocess,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028');P=D.parent/'codex-pv-rdea-20261028'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
b=P/'client-deployed-baseline';assert sha(b)=='fa888460b2c37bee087afd6289cd55219fe2732ea1e1c75011147ed15c260348'
print('Expected time: finite image/ELF metadata aggregation, no rebuild or arithmetic gate.',flush=True)
with lzma.open(P/'machine-stdlib-callers-graph.json.xz','rt') as f:g=json.load(f)
m=json.loads((P/'machine-stdlib-callers.json').read_text());sites=json.loads((P/'site-reconciliation.json').read_text())
U=set(g['functions'].values());assert set(g['edges'])<=U
assert all(set(ds)<=U for ds in g['edges'].values())
# Full-image overapproximation deliberately retains otherwise unresolved register callbacks.
covered=[dict(caller=r['caller'],instruction=r['instruction'],target_domain='ALL_IMAGE_FUNCTION_ENTRIES_OR_DYNAMIC_IMPORTS') for r in m['unresolved_indirect']]
assert all(r['caller'] in U for r in covered)
needed=subprocess.check_output(['readelf','-dW',str(b)],text=True)
imports=subprocess.check_output(['nm','-D','--undefined-only',str(b)],text=True)
ldd=subprocess.check_output(['ldd',str(b)],text=True)
paths=[b]
for line in ldd.splitlines():
 hit=re.search(r'(?:=>\s*)?(/\S+)\s+\(0x',line)
 if hit:paths.append(Path(hit[1]))
public=[]
for p in dict.fromkeys(paths):
 note=subprocess.check_output(['readelf','-nW',str(p)],text=True)
 ids=re.findall(r'Build ID: ([0-9a-f]+)',note)
 public.append(dict(path=str(p),sha256=sha(p),size=p.stat().st_size,build_ids=ids,build_id_bytes=[len(s)//2 for s in ids],locate_build_id_capacity=[23+6+2*(len(s)//2)+1 for s in ids]))
result=dict(binary_sha256=sha(b),image_function_count=len(g['functions']),unique_demangled_names=len(U),original_direct_reachable=len(g['reachable']),all_image_function_entries=g['functions'],all_image_indirect_sites=covered,dynamic_needed=needed,dynamic_imports=imports,ldd=ldd,public_loaded_artifacts=public,method='Conservative whole-image callback target domain; no function is excluded because a register call is unresolved or a direct path is absent.',closed_scope='Every function entry in the statically linked client image and its recorded dynamic imports is retained. This removes unresolved register calls as a reason to omit an image function.',complete_source_reachability_certificate=False,remaining='Source-site/inline completeness and per-invocation guard/header provenance are separate obligations. This overapproximation does not establish that each retained function is reachable or that its invocation guard is public.',source_inventory_sha256=sha(P/'site-reconciliation.json'))
(D/'indirect-closure.json').write_text(json.dumps(result,indent=2)+'\n')
# Classify every retained source candidate without treating missing provenance as a witness.
classify={
0:('DYNAMIC_DIAGNOSTIC','msg.len()+2+Debug(lhs).len()+4+Debug(rhs).len()+1','formatted operands and comparison-failure guard require source caller provenance','UNRESOLVED'),
1:('POW_HEX','2*bytes.len()','native monomorphization/caller exclusion and bytes length origin remain to be certified','UNRESOLVED'),
2:('RESERVATION','69; join basename69, relative','capacity and basename shape derived from fixed array32 and literals; directory is a public caller parameter','SOURCE_SHAPE_PROVED'),
17:('CLIENT_LITERAL_JOINS','note-recovery.json; mask-nonce-ledger; proof.bin; statement.bin','literal path bytes and directory input are public; entry guards include proof completion and need an endpoint provenance certificate','SHAPES_PUBLIC_GUARDS_UNRESOLVED'),
19:('ITERTOOLS_JOIN','sep.len()*iterator.lower_size_hint','no linked generic instantiation was established; retaining as a source candidate rather than claiming absence from nm proves exclusion','UNRESOLVED'),
20:('ITERTOOLS_JOIN','sep.len()*iterator.lower_size_hint','same generic/inline exclusion obligation','UNRESOLVED'),
21:('CPU_ENV_PATH','mount_point + relative cgroup path','arguments and path predicates derive from public /proc and mount metadata; exact runtime candidate binding remains','PUBLIC_ENV_SOURCE_RUNTIME_BINDING_PENDING'),
22:('CPU_ENV_PARAM','base.join(param)','public cgroup file name and public mount base; exact runtime candidate binding remains','PUBLIC_ENV_SOURCE_RUNTIME_BINDING_PENDING')}
rows=[]
for r in sites['MIR_candidates']:
 if r['classification'].startswith('build'):continue
 c=classify[r['id']]
 rows.append(dict(kind='MIR',id=r['id'],function=r['function'],classification=c[0],argument_header=c[1],guard_provenance=c[2],status=c[3],source_sites=r['sites']))
for i,r in enumerate(sites['stdlib']['sites']):
 origin=r['source_origin']['program_name']
 if origin=='format_inner':header='Arguments::estimated_capacity: decoded literal template only; operand lengths are excluded from this initial request';guard='all formatting call sites and their invocation guards must be related to public source data';status='HEADER_SOURCE_PUBLIC_GUARD_UNRESOLVED'
 elif origin=='from_utf8_lossy':header='input byte slice length, after the first invalid-UTF8 chunk';guard='invalid-UTF8 guard and input origin: strerror(error code), addr2line file path; proving the selected error/frame is witness-independent remains';status='INPUT_AND_GUARD_UNRESOLVED'
 elif origin=='locate_build_id':header='23+6+2*build_id.len()+1; build-id bytes belong to public ELF metadata';guard='cache miss, selected module from captured PC, and file availability checks; PC/frame selection provenance remains';status='METADATA_HEADER_PUBLIC_SELECTION_UNRESOLVED'
 elif origin in ['locate_debuglink','locate_debugaltlink','handle_split_dwarf']:header='base path header plus debuglink/debugaltlink/DWARF directory/file payload from public artifact metadata';guard='cache state, captured PC/module/unit choice, metadata presence and filesystem results; complete per-invocation header and guard derivation remains';status='METADATA_ARGUMENT_PUBLIC_SELECTION_UNRESOLVED'
 elif origin=='_join':header='clone base live length; optional separator; path length; owned cleanup69 at the reservation caller';guard='five linked callers have explicit source inventory; actual reservation tail simulation and error cleanup are proved in RDEAC';status='LOCAL_CONSUMER_PROVED_GLOBAL_CALLER_PROVENANCE_PENDING'
 else:raise AssertionError(origin)
 rows.append(dict(kind='STDLIB_INLINE',id=i,function=r['demangled'],source_origin=r['source_origin'],argument_header=header,guard_provenance=guard,status=status,site=r))
assert len(rows)==23
(D/'diagnostic-provenance.json').write_text(json.dumps(dict(binary_sha256=sha(b),entries=rows,source_site_completeness=False,witness_dependent_findings=[],reason='Source-dependent or unclassified is not synonymous with witness-dependent. No pair of admitted same-public witnesses exhibiting a differing diagnostic guard/header was checked. All unresolved selections are retained as blockers, not public assumptions.'),indent=2)+'\n')
# Check all inherited deployed standard-library body pins before connecting cleanup.
checks=[]
for filename in ['v178-deployed-binding.json','v181-deployed-binding.json']:
 x=json.loads((D.parent/'codex-pv-rdb1-20261028'/filename).read_text())
 for r in x['checks']:
  p=Path(r['file']);actual=sha(p);assert actual==r['file_sha256'],p
  checks.append(dict(file=str(p),anchor=r.get('anchor','whole-file/branch check'),sha256=actual))
lib=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
def body(p,anchor):
 s=p.read_text();a=s.index('{',s.index(anchor));j=a+1;depth=1
 while depth:depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[a:j]
extra=[]
for f,anchor,required in [
 ('std/src/path.rs','pub fn join<P: AsRef<Path>>',['self._join(path.as_ref())']),
 ('alloc/src/raw_vec/mod.rs','const fn handle_error(e:',['CapacityOverflow => capacity_overflow()','AllocError { layout, .. } => handle_alloc_error(layout)']),
 ('alloc/src/raw_vec/mod.rs','unsafe impl<#[may_dangle] T, A: Allocator> Drop for RawVec',['self.inner.deallocate(T::LAYOUT)']),
 ('alloc/src/raw_vec/mod.rs','unsafe fn deallocate(&mut self, elem_layout:',['self.current_memory(elem_layout)','self.alloc.deallocate(ptr, layout)']),
 ('alloc/src/vec/mod.rs','unsafe impl<#[may_dangle] T, A: Allocator> Drop for Vec',['ptr::drop_in_place(ptr::slice_from_raw_parts_mut(self.as_mut_ptr(), self.len))'])]:
 p=lib/f;s=body(p,anchor)
 for q in required:assert q in s,(f,anchor,q)
 extra.append(dict(file=str(p),file_sha256=sha(p),anchor=anchor,body=s,required=required))
(D/'cleanup-source-binding.json').write_text(json.dumps(dict(classification='structural (K-1 substitute); library/body boundary and finite native fixture; compiler/primitive adequacy retained',inherited_checked_bodies=checks,extra=extra,native='owned-native-result.json',lean=['PV_RDEAC_FullAppend','PV_RDEAC_FullClone','PV_RDEAC_FullJoin','PV_RDEAC_JoinHandlers','PV_RDEAC_EndpointInstance'],qualifications=['default deployed allocation error handler; no custom alloc_error_handler or oom=panic flag','64-bit native ABI and original valid runtime carrier relation','no complete diagnostic guard/header certificate or headline privacy claim']),indent=2)+'\n')
print('image functions',len(g['functions']),'covered register instructions',len(covered),'source candidates',len(rows),'public artifacts',len(public),flush=True)
