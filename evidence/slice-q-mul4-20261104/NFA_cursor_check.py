from NFA_native_check import *
p=check('NFA_K016',0,'NFA_copy::KMX_checks::KMX_ptr_correct');n=check('NFA_K017',1,'NFA_copy::KMX_checks::KMX_ptr_wrong')
assert p['source_hashes']==n['source_hashes'] and p['env']==n['env']
pairs=[]
for a,b,name,cfg in [('NFA_K012','NFA_K013','dots_cursor_layout','NFA_wrong_cursor_layout'),('NFA_K014','NFA_K015','dots_cursor_arbitrary_prestate','NFA_wrong_cursor_prestate')]:
 h='fast_pairing::canonical::NFA_dot_ctor::'+name;x=check(a,0,h);y=check(b,1,h)
 assert x['source_hashes']==y['source_hashes']==p['source_hashes']
 assert envbase(x)==envbase(y)==p['env']
 assert y['env']['RUSTFLAGS']==x['env']['RUSTFLAGS']+' --cfg '+cfg
 for suffix in ['-graph-check.json','-tool-check.json']:assert obj(E/(a+suffix))==obj(E/(b+suffix))==obj(E/('NFA_K016'+suffix))==obj(E/('NFA_K017'+suffix))
 pairs.append(dict(positive=a,negative=b,harness=h,copy_controls=['NFA_K016','NFA_K017']))
r=obj(E/'NFA_L092/receipt.json');assert r['exit_status']==0
assert all('sorryAx' not in line for line in r['print_axioms'])
for name,h in r['source_hashes'].items():assert sha(E/'NFA_L092/sources'/name)==h
out=dict(status='NATIVE_MODEL_CURSOR_ASSOCIATION_CANDIDATE',native_pairs=pairs,lean_theorems=['AspisR1.NFA_CursorRelation.initial','AspisR1.NFA_CursorRelation.association'],lean_attempt='NFA_L092',model_domain='batch≤7; native.start=4*batch; native.remaining=7-batch; step_minus_one=3; Bool unrestricted. Model.start=min(4*batch,26), model.end=26, model.step=4.',compiler_representation='Calibrated under pinned Kani/Rust compiler only; no portable Rust ABI or source-to-ELF conclusion.',trust='P6/D188 option A semantic transport retained, reclassification only',composed_rows_closed=[])
(E/'NFA_CURSOR_CHECK.json').write_text(json.dumps(out,indent=2)+'\n');print(out['status'])
