"""Read-only source guard/site inventory. No panic payload content is evaluated.
No syntactic inventory is promoted to a universal reached-cone certificate.
"""
from pathlib import Path
import json,hashlib,re,lzma,collections
D=Path('/home/dombarker/project-offloads/codex-pv-diag8-20261029');S=D.parent/'codex-pv-fscan-20261028/src';P=D.parent/'codex-pv-diag-20261029';R=D.parent/'codex-pv-rdea-20261028'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((P/'source-identity.json').read_text())['checks']; files=[];sites=[]
rx=re.compile(r'\b(panic!|assert!|assert_eq!|assert_ne!|debug_assert!|debug_assert_eq!|ensure!|anyhow!|bail!|format!|println!|eprintln!|(?:trace|debug|info|warn|error)!|unwrap\(|expect\()')
for q in pins:
 p=S/q['path']
 assert sha(p)==q['sha256'],q['path']
 if p.suffix!='.rs':continue
 files.append(dict(path=q['path'],sha256=sha(p)))
 fn=''; testline=None
 for i,line in enumerate(p.read_text().splitlines(),1):
  fm=re.search(r'\bfn\s+(\w+)',line)
  if fm:fn=fm[1]
  if '#[cfg(test)]' in line:testline=i
  for m in rx.finditer(line):
   typ=m[1];panic=typ.startswith(('panic','assert','debug_assert','unwrap','expect'))
   sites.append(dict(path=q['path'],line=i,column=m.start()+1,function_hint=fn,site=typ,under_test_marker_candidate=testline,category='panic_guard' if panic else 'format_or_diagnostic',disposition='UNRESOLVED: exact native reachability/canonical invariant or public operand and invocation association required',payload_content_analyzed=False if panic else None))
with lzma.open(D/'source-site-inventory.json.xz','wt') as f:json.dump(dict(files=files,sites=sites,complete_reached_cone=False,fn_hint_not_parser=True),f)
# Statement-level guard mapping; do not inspect the panic payload itself.
def body(rel,first,last,checks):
 p=S/rel; lines=p.read_text().splitlines();text='\n'.join(lines[first-1:last]);cursor=-1
 for check in checks:
  at=text.find(check,cursor+1);assert at>=0,(rel,check);cursor=at
 return dict(path=rel,span=[first,last],file_sha256=sha(p),body_sha256=hashlib.sha256(text.encode()).hexdigest(),ordered_checks=checks)
b=[]
b.append(dict(source=body('crates/aspis-prover/src/state_only_entropy.rs',805,841,['word: 8','fn next_word','if self.word == 8','self.block = profile21_source_expander_block','self.counter = self.counter.wrapping_add(1)','self.word = 0','let start = 4 * self.word','self.word += 1','self.block[start..start + 4]']),model='cursorRun/slot/nextCursor',laws=['cursor_invariant','cursor_panic_guard_false','array_all_cursor_bytes_safe'],steps=['new initializes cursor 8 and block32','refill returns block32; counter wraps separately, never used in slice index','reset cursor before computing start','increment cursor once; index uses saved start','four-byte slice converts to array4; fixed-size conversion cannot fail'],retained=['hash/callback normal-return, destructor/allocator/runtime association and V370','other caller mutation of this private state must follow the same methods'],class_='own-1 local index/control binding; not a whole-source refinement'))
b.append(dict(source=body('crates/aspis-r1-cost-probe/src/prover.rs',37,59,['assert_eq!(q.len(),w.len())','while d<q.len()/4','while s<4','while t<4','let at=s+PERM[t]','c[at]','q[4*d+s]','w[4*d+t]']),laws=['round_query_bound','round_weight_bound','round_coeff_bound','round_equal_shape'],retained=['actual caller q/w length equality; fixed shape is not derived merely from canonical field values']))
b.append(dict(source=body('tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs',27,33,['pub fn nonce','assert_eq!(k, self.entered','self.keys[k]','self.entered += 1']),laws=['publication_callback_bound','publication_callback_order'],retained=['callback sequence 0..entered after retained earlier-attempt effects; native adapter association and cap8']))
# Verify concrete constants before associating arithmetic helpers.
constants={}
for rel,key,expected in [('crates/aspis-r1-cost-probe/src/compact.rs','SPLIT','10'),('crates/aspis-r1-cost-probe/src/weights.rs','PERM','[0,3,2,1]')]:
 p=S/rel;t=p.read_text();m=re.search(r'pub const '+key+r'\s*:\s*[^=]+?=\s*([^;]+);',t);assert m
 actual=re.sub(r'\s','',m[1]);assert actual==expected,(key,actual);constants[key]=dict(value=actual,file_sha256=sha(p),path=rel)
p=S/'crates/aspis-prover/src/state_only_entropy.rs';assert 'const RESERVATION_MAGIC: &[u8; 16]' in p.read_text();constants['reservation_writes']=[16,32,32]
# Exact literal ensure/anyhow sites, with no dynamic formatting placeholders.
messages=[]
for rel in ['tools/r1-cost-probe/src/bin/devnet_spend/Client64_accounts.rs','tools/r1-cost-probe/src/bin/devnet_spend/plan.rs']:
 p=S/rel
 for i,line in enumerate(p.read_text().splitlines(),1):
  if 'ensure!' in line or 'anyhow!' in line:
   messages.append(dict(path=rel,line=i,text=line.strip(),format_placeholders=bool(re.search(r'"[^"\n]*\{',line)),classification='literal text only when no placeholders; guard occurrence/native format execution still required'))
# The dependency log entries in the IR are all conservatively retained.
with lzma.open(R/'machine-relocations-graph.json.xz','rt') as f:machine=json.load(f)
with lzma.open(R/'ir-unit-qualified-graph.json.xz','rt') as f:ir=json.load(f)
logger_targets=[dict(symbol=k,name=v,reachable=k in ir['reachable'],linked=k in ir['linked']) for k,v in ir['names'].items() if any(s in v for s in ['log::__private','log::logger','Log>::log','Log>::enabled'])]
machine_log=[(k,v) for k,v in machine['functions'].items() if any(s in v for s in ['log::__private','log::logger','Log>::log','Log>::enabled'])]
log_summary=dict(targets=logger_targets,machine_logger_entries=machine_log,graph_sha256=sha(R/'machine-relocations-graph.json.xz'),ir_graph_sha256=sha(R/'ir-unit-qualified-graph.json.xz'),honest_reachability_proved=False,remaining='No direct reached log target in inherited graph does not exclude inlined macros or indirect/native callbacks. Each logger-ir-sites entry remains an exact candidate; operand law depends on complete reached-cone binding.')
(D/'source-bindings.json').write_text(json.dumps(dict(bindings=b,constants=constants,literal_sites=messages,logger=log_summary,source_files_checked=len(files),source_sites=len(sites),class_='own-1 local guard dataflow association, partial',compiler_boundary='V370 / D381 / D386 retained',new_trust=0),indent=2)+'\n')
print('files',len(files),'sites',len(sites),'literal sites',len(messages),'logger image entries',len(machine_log))
