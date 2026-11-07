from NNJ_run import *
for a,h,v,c,env in [
 ('NNJ_K003','r1_pool_adapter::NMX_217_native::fidelity::NMX_shape_contract','PASS','decoder_contract',{}),
 ('NNJ_K004','r1_pool_adapter::NMX_217_native::fidelity::NMX_shape_modifies','FAIL','decoder_modifies',{}),
 ('NNJ_K005','r1_pool_adapter::NMX_217_native::NMX_217_wrong_length','FAIL','decoder_inverted_ensures',{'NMX_217_INVERSE':'1'}),
 ('NNJ_K006','r1_pool_adapter::NMX_217_native::NNJ_assignment::NMX_assign_contract','PASS','assignment_contract',{}),
 ('NNJ_K007','r1_pool_adapter::NMX_217_native::NNJ_assignment::NMX_assign_contract','FAIL','assignment_inverted_ensures',{'NMX_217_INVERSE':'1'}),
 ('NNJ_K008','r1_pool_adapter::NMX_217_native::NNJ_assignment::NNJ_assign_real','PASS','assignment_unimplied_real',{}),
 ('NNJ_K009','r1_pool_adapter::NMX_217_native::NNJ_assignment::NNJ_assign_stub','FAIL','assignment_unimplied_stub',{}),
 ('NNJ_K010','r1_pool_adapter::NMX_217_native::NNJ_assignment::NMX_assign_contract','FAIL','assignment_modifies',{'RUSTFLAGS':'--cfg nnj_empty_modifies'}),
]:
 if not run(a,h,v,env,c):raise RuntimeError('Unexpected verdict; stop queue at '+a)
