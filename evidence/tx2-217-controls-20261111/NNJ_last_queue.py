from NNJ_run import *
for a,h,v,c in [
 ('NNJ_K013','r1_pool_adapter::NMX_217_native::NNJ_assignment::NNJ_assign_shape_contract','PASS','assignment_shape_contract'),
 ('NNJ_K014','r1_pool_adapter::NMX_217_native::NNJ_assignment::NNJ_assign_shape_real','PASS','assignment_unimplied_real'),
 ('NNJ_K015','r1_pool_adapter::NMX_217_native::NNJ_assignment::NNJ_assign_shape_stub','FAIL','assignment_unimplied_stub'),
 ('NNJ_K016','NMX_KMX::KMX_checks::KMX_slice_wrong','FAIL','KMX_slice_negative'),
]:
 if not run(a,h,v,{},c):raise RuntimeError('Unexpected verdict at '+a)
