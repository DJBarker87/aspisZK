from gate_common import *
import ast
bundle=json.loads((D.parent/'codex-pv-fscan-20261028/structural-inputs.json').read_text())
old=bundle['tools/pv-relink-20261028/bind-v178.py'];tree=ast.parse(old['text']);expected=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='expected' for t in n.targets))
# Exactly the deployed source changes, with their symbolic laws recorded.
expected=expected.replace('self.inner.clear();','self.inner.truncate(0);').replace('MAIN_SEPARATOR_STR','MAIN_SEP_STR')
check('std/src/path.rs','fn _push(',expected,'V178.truncate_complete,zero_boundary,push_complete; Linux prefix branches absent')
check('std/src/path.rs','pub fn join<P:', '{self._join(path.as_ref())}','AsRef evaluation retained before clone')
check('std/src/path.rs','fn _join(', '{let mut buf=self.to_path_buf();buf.push(path);buf}','V178.join_repaired; clone occurs even on absolute path')
check('std/src/path.rs','pub fn to_path_buf(', '{PathBuf::from(self.inner.to_os_string())}','owned clone before push')
check('std/src/ffi/os_str.rs','pub fn to_os_string(', '{OsString {inner:self.inner.to_owned()}}','preserve byte allocation and clone error')
check('std/src/sys/os_str/bytes.rs','pub fn to_owned(', '{Buf {inner:self.inner.to_vec()}}','base cloned, never skipped for absolute path')
check('std/src/sys/os_str/bytes.rs','pub fn push_slice(', '{self.inner.extend_from_slice(&s.inner)}','V182 reserve-copy law; no String UTF8 assumption on Unix byte carrier')
check('std/src/ffi/os_str.rs','pub fn truncate(', '{self.as_os_str().inner.check_public_boundary(len);unsafe {self.inner.truncate_unchecked(len)};}','V178.zero_boundary: index0 exits before any UTF8 or indexing slow path')
check('std/src/sys/os_str/bytes.rs','fn truncate_unchecked(', '{self.inner.truncate(len);}','V178.truncate_complete')
check('alloc/src/vec/mod.rs','pub fn truncate(', '{unsafe {if len>self.len {return;}let remaining_len=self.len-len;let s=ptr::slice_from_raw_parts_mut(self.as_mut_ptr().add(len),remaining_len);self.len=len;ptr::drop_in_place(s);}}','V178.byte_drops,retained_header; u8 has no destructor; old bytes unchanged')
check('std/src/path.rs','fn prefix_len(', '{if !HAS_PREFIXES {return 0;}self.prefix.as_ref().map(Prefix::len).unwrap_or(0)}','Linux HAS_PREFIXES=false')
check('std/src/path.rs','fn prefix_verbatim(', '{if !HAS_PREFIXES {return false;}self.prefix.as_ref().map(Prefix::is_verbatim).unwrap_or(false)}','Linux false, excludes Windows component collection/normalization')
check('std/src/sys/path/unix.rs','pub fn parse_prefix(', '{None}','Linux prefix absent')
u=(S/'std/src/sys/path/unix.rs').read_text();assert 'pub const HAS_PREFIXES: bool = false;' in u and 'pub const MAIN_SEP_STR: &str = "/";' in u
check('std/src/sys/path/unix.rs','pub fn is_sep_byte(', "{b==b'/'}",'Unix slash constant exact')
boundary=body((S/'std/src/sys/os_str/bytes.rs').read_text(),'fn check_public_boundary(')
prefix='{if index==0 || index==self.inner.len() {return;}'
assert tok(boundary)[:len(tok(prefix))]==tok(prefix)
checks.append(dict(file=str(S/'std/src/sys/os_str/bytes.rs'),file_sha256=hashlib.sha256((S/'std/src/sys/os_str/bytes.rs').read_bytes()).hexdigest(),complete_body=boundary,law='V178.zero_boundary; unconditional return for index0 excludes entire remaining body'))
r=(D/'cblib-owned.rs').read_text();rb=body(r,'pub fn join_slices_reference(')
assert tok(rb)==tok("{if path.len()>0 && path[0]==b'/' {out.extend_from_slice(path);} else {out.extend_from_slice(base);if base.len()>0 && base[base.len()-1]!=b'/' {out.push(b'/');}out.extend_from_slice(path);}}")
for dep in ['v182-deployed-binding.json','v170-deployed-binding.json']:
 for item in json.loads((D/dep).read_text())['checks']:
  if item.get('file_sha256'):assert hashlib.sha256(Path(item['file']).read_bytes()).hexdigest()==item['file_sha256']
j=dict(row='V178',status='FINDING',checks=checks,original_gate_sha256=old['sha256'],old_reference=rb,law='PV_RDB1_V178.join_repaired/clone_failure',inherited='V182 byte append and V170 pointer/slice/drop; every checked source hash revalidated',obstruction='Native always clones base; original absolute-path reference skips clone. Distinct allocation request trace observed for base=base/path=/. Full arbitrary-world/Result equality to old reference false. Historical contents-only claim explicitly retained allocation effects as residual; that narrower claim not refuted.',repaired_statement='Clone base first, then truncate0 or append separator and append path, with the same allocator and error handlers. For any complete-Result clone/append operations sourceJoin equals repaired reference including failure and world.',features=dict(path='resolved-features.json',sha256=hashlib.sha256((D/'resolved-features.json').read_bytes()).hexdigest()),toolchain='1.94.1',profile='release opt3 debug_assertions=false overflow_checks=false panic=unwind',native='result-effect-witness/receipt.json; native-join/receipt.json finite only',new_trust_items=[])
(D/'v178-deployed-binding.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS V178 deployed path/truncate binding; FINDING old full-world promotion rejected')
