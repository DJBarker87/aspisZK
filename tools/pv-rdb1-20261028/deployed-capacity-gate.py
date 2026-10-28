from gate_common import *
check('alloc/src/string.rs','pub fn with_capacity(', '{String {vec:Vec::with_capacity(capacity)}}','V181.complete; V181Finding.overflow_world')
check('alloc/src/vec/mod.rs','pub const fn with_capacity(', '{Self::with_capacity_in(capacity,Global)}','Global selected')
check('alloc/src/vec/mod.rs','pub fn with_capacity_in(', '{Vec {buf:RawVec::with_capacity_in(capacity,alloc),len:0}}','V181.empty_value; capacity representation retained')
check('alloc/src/raw_vec/mod.rs','pub(crate) fn with_capacity_in(', '{Self {inner:RawVecInner::with_capacity_in(capacity,alloc,T::LAYOUT),_marker:PhantomData,}}','u8 layout size1 align1')
s=(S/'alloc/src/raw_vec/mod.rs').read_text();a=s.index('fn with_capacity_in(capacity: usize, alloc: A, elem_layout: Layout)')
actual=body(s[a:],'fn with_capacity_in(')
want='{match Self::try_allocate_in(capacity,AllocInit::Uninitialized,alloc,elem_layout) {Ok(this)=>{unsafe {hint::assert_unchecked(!this.needs_to_grow(0,capacity,elem_layout));}this}Err(err)=>handle_error(err),}}'
assert tok(actual)==tok(want)
checks.append(dict(file=str(S/'alloc/src/raw_vec/mod.rs'),file_sha256=hashlib.sha256(s.encode()).hexdigest(),complete_body=actual,law='V181.complete; same handler and allocator error/private world retained'))
check('alloc/src/raw_vec/mod.rs','fn try_allocate_in(', '''{let layout=match layout_array(capacity,elem_layout) {Ok(layout)=>layout,Err(_)=>return Err(CapacityOverflow.into()),};if layout.size()==0 {return Ok(Self::new_in(alloc,elem_layout.alignment()));}let result=match init {AllocInit::Uninitialized=>alloc.allocate(layout),#[cfg(not(no_global_oom_handling))]AllocInit::Zeroed=>alloc.allocate_zeroed(layout),};let ptr=match result {Ok(ptr)=>ptr,Err(_)=>return Err(AllocError {layout,non_exhaustive:()}.into()),};Ok(Self {ptr:Unique::from(ptr.cast()),cap:unsafe {Cap::new_unchecked(capacity)},alloc,})}''','V181.complete; zero_world; V183 layout/pointer/allocator effects')
check('alloc/src/raw_vec/mod.rs','fn handle_error(', '{match e.kind() {CapacityOverflow=>capacity_overflow(),AllocError {layout,..}=>handle_alloc_error(layout),}}','overflow panics; OOM abort retained, never mapped to ok')
prior=json.loads((D/'v183-deployed-binding.json').read_text())
for item in prior['checks']:
 if item.get('file_sha256'):assert hashlib.sha256(Path(item['file']).read_bytes()).hexdigest()==item['file_sha256']
ref=(D/'cblib-owned.rs').read_text();old=body(ref,'pub fn string_capacity_reference(')
assert tok(old)==tok('{String::new()}')
fixed=(D/'capacity-reference.rs').read_text();rb=body(fixed,'pub fn deployed_capacity_reference(')
assert tok(rb)==tok('{let mut value=String::new();value.reserve_exact(n);value}')
j=dict(row='V181',status='FINDING',checks=checks,old_reference=old,repaired_reference=rb,repaired_law='PV_RDB1_V181.complete/with_handlers',obstruction='Old reference always returns empty; deployed n=isize::MAX+1 panics before allocation. No unconditional native complete-Result association to old reference. Returning empty-value and historical bounded/source-image claims not refuted.',lean=['54734-receipt.json','54736-receipt.json'],inherited_deployed_laws='v183-deployed-binding.json: every file hash revalidated',features=dict(path='resolved-features.json',sha256=hashlib.sha256((D/'resolved-features.json').read_bytes()).hexdigest()),toolchain='1.94.1',profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',new_trust_items=[])
(D/'v181-deployed-binding.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS V181 deployed constructor binding; FINDING old unconditional Result promotion rejected')
