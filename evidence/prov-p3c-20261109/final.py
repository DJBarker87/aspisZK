import json,re,lzma,glob
items=json.load(open('../prov-p2g-20261109/PCUG_FOR_P3.json'))['items']
runs={'RPu_FIq_Native01':'PCVC_L022','RPu_FIq_Native02':'PCVC_L023','RPu_FIq_Native04':'PCVC_L027','RPu_FIq_Native05':'PCVC_L028','RPu_FIq_Native06':'PCVC_L026','RPu_FIq_Native07':'PCVC_L029','RPu_FIq_Native08':'PCVC_L038','RPu_FIq_Native09':'PCVC_L040','RPu_FIq_Native10':'PCVC_L047','RPu_FIq_Native11':'PCVC_L039'}
proved={}
for m,L in runs.items():
    r=json.load(open(f'{L}/receipt.json')); assert r['exit_status']==0,(m,L)
    log=lzma.open(f'{L}/stdout.log.xz','rt').read()
    ok=re.findall(r"'PRVC\.Eq\.(\S+)' (?:does not depend on any axioms|depends on axioms: \[([^\]]*)\])",log)
    good=[n for n,a in ok if 'sorryAx' not in a and all(x.strip() in ('propext','Classical.choice','Quot.sound') for x in a.split(',') if x.strip())]
    proved[m]=(L,set(good),r)
TD={'pool_v1.pair_forest_accounts.digest_is_canonical_loop.body':'refinement body_refines (Option Bool -> Bool via conv)','pool_v1.pair_forest_accounts.digest_is_canonical_loop':'refinement loop_refines (conv)','pool_v1.pair_forest_accounts.digest_is_canonical':'digest_is_canonical_eq (plain equality)','pool_v1.pair_forest_accounts.pool_v1_pair_forest_output_lane_v1':'output_lane_eq (plain equality)'}
status=[];remaining=[];cls=[]
reason={'ARRAY_FROM_FN_LIBRARY':'core.array.from_fn is an axiom in the original emission; gate uses array_from_fn_copy (hand model, see PCVC_HAND_MODELS.json)','FRESH_DID_NOT_ELABORATE':'fresh declaration does not elaborate against the gate environment (depends on core.array.from_fn or another missing library constant); dropped by P2g','CONST_MONADIC_BINDING':'needs constant-binding lemma Fresh.CONST = ok Gate.CONST (not completed in this run)','EXTERNAL_P_AXIOM':'see P2f TD_HP result','CONFIG_OFF_REQUIRED':'gate bodies require overflow OFF emission; see PCVC_NEED_EXTRACTION.json','BLOCKED_BY_CALLEE':'blocked by an open callee','LOOP_ENCODING_OR_CALLER':'loop bridge not closed in this run','FRESH_ELABORATION_TIMEOUT':'fresh section of module does not elaborate within 180 s (PCVC_L034/L042/L043: base alone); shape retired','HEARTBEAT_TIMEOUT':'not attempted','BODY_EQUAL_UP_TO_CRATE_PREFIX_CALLEE_NOT_EQUATED':'not attempted'}
for i in items:
    if i['status']=='TEXT_IDENTICAL_ONLY': continue
    mod=i['module']; d=i['definition'].split('.',1)[1]
    rec={'module':mod,'definition':d,'p2g_class':i.get('diff_class') or i['status']}
    if mod in proved and d in proved[mod][1]:
        rec.update(result='PROVED_P3',attempt=proved[mod][0],theorem='PRVC.Eq.'+d,file=f'PRVEq_{mod}_P3.lean',classification='SOURCE_SHAPE',tool_difference=i.get('diff_class'))
        status.append(rec)
    elif mod=='AspisR1TerminalDecoder.Funs' and d in TD:
        rec.update(result='DISCHARGED_BY_P2F',via='evidence/prov-p2f-20261109/PRVEq_TD_HP_P3f.lean (PCUF_L015 exit 0): '+TD[d],classification='SOURCE_SHAPE',note='loop-return encoding Option Bool vs Bool, not a semantic difference; gate module flagged non-frozen by PCXA')
        status.append(rec)
    else:
        rec.update(result='OPEN',reason=reason.get(i.get('diff_class'),i.get('diff_class') or i['status']))
        remaining.append(rec)
extra=[{'module':'AspisR1WithdrawalCaller.Funs','definition':'pool_v1.payment_relation.validate_common','result':'PROVED_P3','attempt':'PCVC_L046','theorem':'PRVC.Eq.validate_common','file':'PRVEq_AspisR1WithdrawalCaller_Funs_P3.lean','classification':'SOURCE_SHAPE','tool_difference':'constant path: fresh pool_v1.incremental_merkle.POOL_V1_LEAF_CAPACITY vs gate pool_v1.POOL_V1_LEAF_CAPACITY; both are 1#u64 <<< 20#usize (tree_depth, leaf_capacity proved)','P3b_class_corrected_from':'SEMANTIC'},
{'module':'AspisR1WithdrawalCaller.Funs','definition':'pool_v1.payment_relation.validate_pool_v1_withdrawal_public_v1','result':'PROVED_P3','attempt':'PCVC_L046','theorem':'PRVC.Eq.validate_pool_v1_withdrawal_public_v1','file':'PRVEq_AspisR1WithdrawalCaller_Funs_P3.lean','classification':'SOURCE_SHAPE','tool_difference':'spend.VALUE_LIMIT vs VALUE_LIMIT (both 1#u32 <<< 30#i32) and validate_common','P3b_class_corrected_from':'SEMANTIC'}]
status+=extra
json.dump({'schema':'PCVC_STATUS/1','target_established':False,'proved_or_discharged':status,'counts':{'proved_P3':sum(1 for s in status if s['result']=='PROVED_P3'),'discharged_by_p2f':sum(1 for s in status if s['result']=='DISCHARGED_BY_P2F'),'open':len(remaining)}},open('PCVC_STATUS.json','w'),indent=1)
json.dump({'schema':'PCVC_REMAINING/1','target_established':False,'items':remaining},open('PCVC_REMAINING.json','w'),indent=1)
print(json.loads(open('PCVC_STATUS.json').read())['counts'])
import collections
print(collections.Counter((r['module'],r['reason'][:40]) for r in remaining))
