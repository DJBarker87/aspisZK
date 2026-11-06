from NLK_lane_invocation import *
def attempt(a,mode,field="all",control_style="negate"):
 start=ORIGINAL.index('    if next_leaf_index == 0');segment=ORIGINAL[start:ORIGINAL.rfind('\n}')]
 body=segment.replace('    Ok(Box::new(PoolV1PairForestLaneStateV1 {','    let boxed=Box::new(PoolV1PairForestLaneStateV1 {').replace('    }))','    }); allocated=(&*boxed as *const PoolV1PairForestLaneStateV1) as usize;Ok(boxed)')
 text=COMMON+HELP+ANN+'''fn stage(){
 use v7_pair_empty_roots::V7_PAIR_EMPTY_ROOTS;
 let bytes:[u8;73]=kani::any();let master:[u8;32]=kani::any();let next_leaf_index:u64=kani::any();let root=digest();let raw:[[u32;8];20]=kani::any();let frontier=raw.map(|r|r.map(M31));let i:usize=kani::any();let row:usize=kani::any();let word:usize=kani::any();kani::assume(i<32&&row<20&&word<8);
 let mut allocated=0usize;let out=(||->Result<Box<PoolV1PairForestLaneStateV1>,ProgramError>{BODY})();
 let expected=next_leaf_index!=0||root==V7_PAIR_EMPTY_ROOTS[20];let mut good=match out{Ok(v)=>expected&&v.bump==bytes[72]&&v.lane_id==bytes[5]&&v.master[i]==master[i]&&v.tree.next_leaf_index==next_leaf_index&&v.tree.root[word].0==root[word].0&&v.tree.frontier[row][word].0==raw[row][word]&&(&*v as *const PoolV1PairForestLaneStateV1) as usize==allocated,Err(e)=>!expected&&e==ProgramError::InvalidAccountData&&allocated==0};
 CORRUPT assert!(good,"post-loop terminal rejection full Result actual allocation-site owned carrier and all windows");}
'''.replace('BODY',body).replace('CORRUPT','good=!good;' if mode=='inverse' else '')
 if field!='all':
  begin=text.index('let mut good=match out{Ok(v)=>')
  end=text.index(';\n ',begin)
  prop={'scalar':'v.bump==bytes[72]&&v.lane_id==bytes[5]&&v.master[i]==master[i]&&v.tree.next_leaf_index==next_leaf_index','root':'v.tree.root[word].0==root[word].0','frontier':'v.tree.frontier[row][word].0==raw[row][word]','owner':'(&*v as *const PoolV1PairForestLaneStateV1) as usize==allocated'}[field]
  text=text[:begin]+'let mut good=match out{Ok(v)=>expected&&'+prop+',Err(e)=>!expected&&e==ProgramError::InvalidAccountData&&allocated==0}'+text[end:]
  text=text.replace('let out=(||','let out=(||')
 if control_style=='returned_scalar':
  assert mode=='inverse' and field=='scalar'
  text=text.replace('let out=(||','let mut out=(||').replace('let mut good=match out','if let Ok(v)=out.as_mut(){v.bump^=1;}let mut good=match out').replace('good=!good;','')
 mod='NLK_lane_suffix'
 (E/(a+'_CUT.json')).write_text(json.dumps(dict(source=P,segment=segment,segment_sha256=sha(segment.encode()),mode=mode,field=field,control_style=control_style,domain='arbitrary post-loop source state; full scalar/root/frontier windows and actual Box identity; source header domain is upstream',retired_predecessor='NLK_K025 whole-invocation scalar timeout; split at post-loop boundary; no timeout/cap/unwind increase',limits='native returning allocation only; universal reservation supplied by NKY allocation interpretation in Lean'),indent=1)+'\n')
 (E/(a+'.patch')).write_text('--- /dev/null\n+++ b/'+mod+'.rs\n@@ -0,0 +1,'+str(len(text.splitlines()))+' @@\n'+''.join('+'+l for l in text.splitlines(True)))
 return submit(a,'r1_pool_adapter::'+mod+'::stage',P,mod,text,mode)
if __name__=='__main__':
 import sys
 attempt(*sys.argv[1:])
