"""Concrete current MIR/source association, without native semantics claim."""
from pathlib import Path
import json,hashlib,re
D=Path(__file__).resolve().parent;ROOT=D.parents[2]
E=ROOT/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/resume-mir';M=E/'mir'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def inspect():
 files={}
 def load(name):
  p=M/name;files[name]=sha(p);return p.read_text()
 def mir(stem):return load(stem+'.ElaborateDrops.after.mir')
 def blocks(t):return dict(re.findall(r'^    (bb\d+)(?: \(cleanup\))?: \{\n(.*?)^    \}',t,re.M|re.S))
 def contains(t,*xs):
  for x in xs:assert x in t,x
 prefix='prover_rw_resume_scalar.Instrumented-'
 draw=mir(prefix+'{impl#1}-draw');resume=mir(prefix+'{impl#2}-resume');run=mir(prefix+'run');hook=mir('zeroize.{impl#31}-drop')
 db=blocks(draw);rb=blocks(resume);ub=blocks(run);hb=blocks(hook)
 contains(db['bb0'],'_3 = [const 0_u8; 64]','::new(move _3)')
 contains(db['bb2'],'_4 = fill(move _5) -> [return: bb3, unwind: bb6]')
 contains(db['bb3'],'StorageDead(_5)','StorageDead(_6)','_8 = move _1','_9 = move _2','_10 = copy _4','request: move _8, bytes: move _9, outcome: move _10')
 contains(rb['bb0'],'_2 = move (_1.0:','_3 = move (_1.1:','_4 = copy (_1.2:')
 contains(rb['bb21'],'_58 = move _13','_59 = move _15','mask_nonce: move _57, field_mask_entropy: move _58, leaf_salt_seed: move _59')
 contains(rb['bb23'],'Some(move _56)');contains(rb['bb24'],'Ok(move _55)');contains(rb['bb25'],'_0 = (move _53, move _54)')
 for b,nxt in [('bb26','bb40'),('bb40','bb41'),('bb41','bb42')]:contains(rb[b],'goto -> '+nxt)
 contains(rb['bb42'],'drop(_3) -> [return: bb43');contains(rb['bb44'],'return;')
 assert all('drop(' not in rb[b] for b in ['bb21','bb22','bb23','bb24','bb25','bb26','bb40','bb41'])
 contains(rb['bb29'],'AddWithOverflow(copy (_2.1: usize), const 1_usize)')
 contains(rb['bb30'],'(_2.1: usize) = move (_60.0: usize)','switchInt(move _61) -> [0: bb34, otherwise: bb31]')
 for b,owner,nxt in [('bb36','_15','bb37'),('bb37','_13','bb38'),('bb38','_3','bb39')]:contains(rb[b],f'drop({owner}) -> [return: {nxt}')
 contains(rb['bb3'],'_7 = copy ((_4 as Err).0: getrandom::Error)','_12 = copy _7','::from(move _12)')
 contains(rb['bb4'],'Err(move _11)','_0 = (move _9, move _10)')
 contains(ub['bb12'],'StorageDead(_23)','_26 = move _27(move _28) -> [return: bb13, unwind: bb32]')
 contains(ub['bb16'],'_58 = const false','_57 = const true','_35 = move ((((_11 as Ok).0:')
 contains(ub['bb24'],'_45 = copy (*_46)[_48]','StorageDead(_46)','StorageDead(_41)','_57 = const false','_51 = move _35','std::mem::drop::<Instrumented::StateOnlyAttemptSecrets>(move _51)')
 contains(ub['bb66'],'switchInt(copy _57) -> [0: bb32, otherwise: bb65]')
 contains(ub['bb70'],'switchInt(copy _58) -> [0: bb34, otherwise: bb69]')
 assert not re.search(r'let(?: mut)? _\d+: bool;.*const (?:true|false)',resume,re.S) # no retained boolean flags in this resume pass
 contains(hb['bb1'],'_4 = &((*_1).0: Z)','observe(move _4, move _5)')
 contains(hb['bb2'],'StorageDead(_4)','_7 = &mut ((*_1).0: Z)','zeroize(move _7)')
 contains(hb['bb3'],'StorageDead(_7)','_9 = copy _3','_11 = &((*_1).0: Z)','observe(move _11, move _12)')
 contains(hb['bb4'],'StorageDead(_11)','record(move _9, move _10)')
 nll=load('zeroize.{impl#31}-drop.nll.0.mir')
 contains(nll,"| '?3 | U0 | {bb1[3..=6]}","| '?4 | U0 | {bb2[5..=6]}","| '?5 | U0 | {bb3[7..=10]}","bw0: issued at bb1[3] in '?3","bw1: issued at bb2[5] in '?4","bw2: issued at bb3[7] in '?5")
 observer=mir('zeroize.{impl#5}-prover_rw_resume_scalar_observe')
 contains(observer,'_11 = &(*_1)[_12]','_20 = &(*_1)[_21]','_17 = const 0_u8','Observation { len: const N, low: move _28, high: move _29 }')
 byte=load('zeroize.{impl#1}-prover_rw_resume_scalar_byte.runtime-optimized.after.mir');contains(byte,'_2 = copy (*_1)','Some(move _2)')
 record=mir('zeroize.ProverRwResumeScalar-record');allocations=dict(re.findall(r'(alloc\d+) \(static: (\w+),',record))
 assert set(allocations.values())=={'COUNT','OVERFLOW','E0','E1','E2'}
 glue=load('core.ptr-drop_in_place.Instrumented__StateOnlyAttemptSecrets.AddMovesForPackedDrops.before.mir');gb=blocks(glue)
 contains(gb['bb7'],'drop(((*_1).1: zeroize::Zeroizing<[u8; 32]>)) -> [return: bb6');contains(gb['bb6'],'drop(((*_1).2: zeroize::Zeroizing<[u8; 32]>))')
 # Full unwind bodies are retained in files, never removed by this association.
 return dict(schema='ProverRwResumeMIR-role-association-v1',input_sha256=files,
  draw=dict(bytes='_2 -> _9 -> return0.bytes',outcome='fill return _4 copied to _10 -> return0.outcome',normal_drop_flags='none retained; normal moved-from drops eliminated',blocks={b:db[b] for b in ['bb0','bb1','bb2','bb3','bb6']}),
  resume=dict(request='_2',bytes='_3',field='_13',leaf='_15',owner='_56 -> _55.Some -> _54.Ok -> return0.1',success_blocks=['bb21','bb22','bb23','bb24','bb25','bb26','bb40','bb41','bb42','bb43','bb60','bb58','bb44'],rejection_drops=['bb36:_15','bb37:_13','bb38:_3'],error_blocks=['bb3','bb4','bb5','bb42'],normal_drop_flags='none retained; static move-path elimination, not reconstructed flags'),
  run=dict(owner='result_11.Ok.Some -> owner_35 -> temp_51 -> mem::drop',phase='bb12 before owner move bb16',copies=['bb20:_35.0[j] -> _37','bb22:field via _41 -> _40','bb24:leaf via _46 -> _45'],raw_boolean_assignments=re.findall(r'^        _(?:54|55|56|57|58) = const (?:true|false);$',run,re.M),raw_flag_blocks={b:ub[b] for b in ['bb0','bb2','bb16','bb24','bb26','bb28','bb65','bb66','bb69','bb70']},flag_roles={'_57':'owner_35 initialized; false before move to drop argument','_58':'result_11.Ok.Some payload initialized; false at owner move','_54/_55/_56':'retained elaborator scaffolding; exact assignments/branches in full MIR; no invented owner role'}),
  drop=dict(active_place='(*self_1).0',NLL_loans=[dict(borrow='bw0',region="'?3",points='bb1[3..=6]',kind='shared pre'),dict(borrow='bw1',region="'?4",points='bb2[5..=6]',kind='mutable zeroize'),dict(borrow='bw2',region="'?5",points='bb3[7..=10]',kind='shared post')],copy_return='Observation usize/u8/u8; no source reference escapes',record_static_allocations=allocations),
  established='current pinned compiler/source normal-path move/drop/loan/static role association only',unwind='full built/NLL/drop-elaborated/optimized dumps retained; not proved',native_projection=False,full_axioms='N/A: no new Lean declarations')
if __name__=='__main__':
 out=inspect();(E/'association.json').write_text(json.dumps(out,indent=2)+'\n');print('Current scalar MIR roles, flags, NLL loans and static stores associated; native projection unproved')
