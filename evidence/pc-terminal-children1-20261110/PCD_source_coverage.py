from pathlib import Path
import subprocess,hashlib,json,re
E=Path(__file__).resolve().parent;rev='b936275465600469312d1f058cdc91ea2a11f3dc';path='programs/aspis-pool/src/pair_forest.rs'
source=subprocess.check_output(['git','show',rev+':'+path],text=True)
start=source.index('fn next_pair_forest_lane_v1(');opening=source.index('{',start);depth=1;end=opening+1
while depth:
 if source[end]=='{':depth+=1
 elif source[end]=='}':depth-=1
 end+=1
function=source[start:end];body=source[opening+1:end-1]
meta=json.loads((E/'PCD_NATIVE_PATCH_META.json').read_text());assoc=json.loads((E/'PCD_FRAGMENT_ASSOCIATION.json').read_text());spans=assoc['spans']
assert all(q['span'] in function and hashlib.sha256(q['span'].encode()).hexdigest()==q['span_sha256'] for q in spans)
step=spans[0]['span'];tail=spans[1]['span'];guard=spans[2]['span']
expected='''
    let afterstate = result.verified_afterstate;
    if GUARD {
        return Err(PoolV1ProgramError::StateHistoryMismatch.into());
    }
    for (level, node) in afterstate.next_frontier.iter().enumerate() {
STEP
    }
TAIL
'''.replace('GUARD',guard).replace('STEP',step).replace('TAIL',tail)
normalize=lambda s:re.sub(r'\s+','',s)
assert normalize(body)==normalize(expected),'STOP: uncovered/reordered frozen source statement'
refs=(E/'PCD_lane_reference.rs').read_text();pins=json.loads((E/'PCD_EXTRACTION_PINS.json').read_text());assert hashlib.sha256(refs.encode()).hexdigest()==pins['rust_reference_sha256']
def function_body(text,name):
 a=text.index('fn '+name+'(');a=text.index('{',a);d=1;b=a+1
 while d:
  d+=int(text[b]=='{')-int(text[b]=='}');b+=1
 return text[a+1:b-1]
assert normalize(function_body(refs,'checked_next'))==normalize(function_body((E/'PCD_guard_native.rs').read_text(),'PCD_checked_reference'))
assert normalize(function_body(refs,'frontier_step'))==normalize(function_body((E/'PCD_frontier_native.rs').read_text(),'PCD_frontier_reference'))
fragment=meta['suffix']
assert 'cursor.next()' in fragment and 'core::ptr::eq(node, &afterstate.next_frontier[level])' in fragment
assert 'assert!(native_level == level)' in fragment
errsource=subprocess.check_output(['git','show',rev+':programs/aspis-pool/src/error.rs'],text=True)
assert 'StateHistoryMismatch = 0x4153_2003' in errsource and 'Self::Custom(error as u32)' in errsource
# Planted source-association faults must each be rejected by the same checks.
checks=[]
for name,mutant in [
 ('extra_effect',body.replace('    let afterstate','    unknown_effect();\n    let afterstate',1)),
 ('missing_guard',body.replace('    if '+guard, '    if false',1)),
 ('wrong_loop',body.replace('next_frontier.iter().enumerate()', 'next_frontier.iter().enumerate().rev()',1)),
 ('wrong_master',body.replace('master: lane.master','master: [0u8;32]',1)),
 ('wrong_bump',body.replace('bump: lane.bump','bump: 0',1)),
 ('wrong_lane',body.replace('lane_id: lane.lane_id','lane_id: 0',1)),
 ('wrong_root',body.replace('root: afterstate.next_root','root: lane.tree.root',1)),
 ('wrong_frontier',body.replace('frontier: afterstate.next_frontier','frontier: lane.tree.frontier',1)),
 ('wrong_index',body.replace('next_leaf_index: afterstate.next_pair_index','next_leaf_index: lane.tree.next_leaf_index',1)),
 ('wrong_error',body.replace('StateHistoryMismatch','InvalidVerifierReturnData',1)),
]:
 assert mutant!=body,name
 rejected=normalize(mutant)!=normalize(expected);assert rejected,name
 checks.append(dict(name=name,rejected=rejected))
rows=[]
for n,line in enumerate(function.splitlines(),source[:start].count('\n')+1):
 if not line.strip():continue
 rows.append(dict(line=n,source=line,category='signature' if n<source[:opening].count('\n')+1 else 'native guard/loop/returned-record and symbolic fold'))
out=dict(status='SOURCE_COVERAGE_PASS_ONLY; not a row promotion',row='POOL:320',revision=rev,source=path,source_sha256=hashlib.sha256(source.encode()).hexdigest(),function_sha256=hashlib.sha256(function.encode()).hexdigest(),body_sha256=hashlib.sha256(body.encode()).hexdigest(),lines=rows,spans=spans,reference_source_sha256=pins['rust_reference_sha256'],error_conversion_source_sha256=hashlib.sha256(errsource.encode()).hexdigest(),mutations=checks,missing='actual-body extraction eligibility, final native controls, full formal/source certificate and coherent gate')
(E/'PCD_SOURCE_COVERAGE.json').write_text(json.dumps(out,indent=1)+'\n')
(E/'PCD_FROZEN_FUNCTION.rs.txt').write_text(function+'\n')
print('PCD source coverage passes for every frozen POOL:320 statement; ten planted correspondence faults rejected; no row promoted.')
