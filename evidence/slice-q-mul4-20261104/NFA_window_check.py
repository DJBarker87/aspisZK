from NFA_native_check import *
p=check('NFA_K021',0,'NFA_copy::KMX_checks::KMX_ptr_correct');n=check('NFA_K022',1,'NFA_copy::KMX_checks::KMX_ptr_wrong')
x=check('NFA_K019',0,'fast_pairing::canonical::NFA_dot_ctor::dots_tail_source_window');y=check('NFA_K020',1,'fast_pairing::canonical::NFA_dot_ctor::dots_tail_source_window')
assert x['source_hashes']==y['source_hashes']==p['source_hashes']==n['source_hashes']
assert envbase(x)==envbase(y)==p['env']==n['env']
assert y['env']['RUSTFLAGS']==x['env']['RUSTFLAGS']+' --cfg NFA_wrong_tail_source_window'
for suffix in ['-graph-check.json','-tool-check.json']:assert obj(E/('NFA_K019'+suffix))==obj(E/('NFA_K020'+suffix))==obj(E/('NFA_K021'+suffix))==obj(E/('NFA_K022'+suffix))
failed=obj(E/'NFA_K018/receipt.json');assert failed['exit_status']==124
out=dict(status='SPLIT_NATIVE_SOURCE_WINDOW_PASS_FULL_JOIN_OPEN',positive='NFA_K019',negative='NFA_K020',copy_controls=['NFA_K021','NFA_K022'],domain='slot<4, position<3, byte<16; arbitrary complete608-byte q and29-cell typed g; no field arithmetic',lean_domain_theorems=['AspisR1.NFA_TailCounter.windows','NEV_DotInputs.selected','AspisR1.NFA_TailQM.source'],excluded_timeout=dict(attempt='NFA_K018',exit_status=124,wall_seconds=failed['wall_seconds'],peak_rss_kib=failed['peak_rss_kib'],swaps=failed['swaps'],no_unchanged_rerun=True),remaining='Lean/KMX frame and complete same-receiver three-push/finish/add physical composition; no composed row credit')
(E/'NFA_WINDOW_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
