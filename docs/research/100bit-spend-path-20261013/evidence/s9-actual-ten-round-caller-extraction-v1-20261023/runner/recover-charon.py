from pathlib import Path
import hashlib,json,re
W=Path(__file__).resolve().parent;R=W/'runs/charon';P=R/'actual-semantic-rounds.llbc'
assert not (R/'receipt.json').exists()
cmd=json.loads((R/'command.json').read_text());obj=json.loads(P.read_text());fds=[f for f in obj['translated']['fun_decls'] if isinstance(f,dict)]
roots=[f for f in fds if any(x.get('Ident',[None])[0]=='semantic_rounds' for x in f.get('item_meta',{}).get('name',[]) if isinstance(x,dict))]
assert obj['has_errors'] is False and len(roots)==1 and roots[0].get('body')
t=(R/'time.log').read_text();status=int(re.search(r'Exit status: (\d+)',t).group(1));assert status==0
swaps=int(re.search(r'Swaps: (\d+)',t).group(1));assert swaps==0
rec={**cmd,'exit_status':status,'wrapper_exit_status':1,'tool_status_source':'GNU time exit status','wall_time_reported_by_time':re.search(r'Elapsed .*?: (\S+)',t).group(1),'peak_process_rss_kib':int(re.search(r'Maximum resident set size \(kbytes\): (\d+)',t).group(1)),'process_swaps':swaps,'scope_memory_peak_bytes':None,'scope_swap_current_bytes':None,'scope_metrics_status':'not persisted: wrapper failed in post-run metadata parsing before writing receipt; verified memory.swap.max=0 cap and GNU time zero swaps retained','recovery_reason':'fun_decls contains null entries; original walker attempted f.get on None after child success. Original runner preserved unchanged; no extraction rerun.','llbc_sha256':hashlib.sha256(P.read_bytes()).hexdigest(),'llbc_bytes':P.stat().st_size,'llbc_has_errors':obj['has_errors'],'llbc_nonnull_fun_decl_count':len(fds),'semantic_rounds_root_count':len(roots),'root_body_nonempty':True,'root_metadata':[{k:f.get(k) for k in ['def_id','item_meta','signature']} for f in roots]}
(R/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:rec[k] for k in ['exit_status','wrapper_exit_status','peak_process_rss_kib','process_swaps','llbc_sha256','semantic_rounds_root_count','root_body_nonempty','scope_metrics_status']}))
