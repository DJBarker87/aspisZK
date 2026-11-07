from NNJ_run import *
for a,h,v,c in [
 ('NNJ_K011','r1_pool_adapter::NMX_217_native::NNJ_assignment::NNJ_assign_real','PASS','assignment_unimplied_real'),
 ('NNJ_K012','r1_pool_adapter::NMX_217_native::NNJ_assignment::NNJ_assign_stub','FAIL','assignment_unimplied_stub'),
 ('NNJ_K013','NMX_KMX::KMX_checks::KMX_slice_wrong','FAIL','KMX_slice_negative'),
 ('NNJ_K014','NMX_KMX::KMX_checks::KMX_ptr_wrong','FAIL','KMX_ptr_negative'),
 ('NNJ_K015','NMX_KMX::KMX_checks::KMX_slice_correct','PASS','KMX_slice_positive'),
 ('NNJ_K016','NMX_KMX::KMX_checks::KMX_ptr_correct','PASS','KMX_ptr_positive'),
]:
 # Copy controls are independent of an assignment fidelity result.
 # An unexpected result must be inspected before any next scope is submitted.
 if not run(a,h,v,{},c):raise RuntimeError('Unexpected verdict at '+a)
