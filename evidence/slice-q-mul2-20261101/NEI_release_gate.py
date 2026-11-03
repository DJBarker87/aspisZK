"""Canonical release domains and exact operator-specific source/cut proofs."""
CANONICAL={'m_add','m_sub','m_double','cm_add','cm_sub','cm_mul','by_r','qm_add','qm_sub','qm_mul','mul_u','wide_add','wide_sub','wide_mul'}
CUTS={
 'm_double':['NEI_NEB_AdditiveCalls.base_double_arguments'],
 'cm_add':['NEI_NEB_FieldDomains.cm_arguments','NEI_NEB_FieldDomains.cm_add_calls'],
 'cm_sub':['NEI_NEB_FieldDomains.cm_arguments','NEI_NEB_FieldDomains.cm_sub_calls'],
 'cm_mul':['NEI_NEB_FieldDomains.cm_arguments','NEI_NEB_CMCalls.multiply','NEI_NEB_NativeFieldScalars.cross_checked'],
 'cm_mul_m31':['NEI_NEB_CMCalls.scale'],
 'by_r':['NEI_NEB_ByRCalls.source'],
 'qm_add':['NEI_NEB_QMCalls.add'], 'qm_sub':['NEI_NEB_QMCalls.sub'],
 'qm_mul':['NEI_NEB_QMCalls.multiply'], 'qm_mul_m31':['NEI_NEB_AdditiveCalls.qm_scale'],
 'mul_u':['NEI_NEB_ByRCalls.mul_u'],
 'wide_add':['NEI_NEB_AdditiveCalls.wide_add'],
 'wide_sub':['NEI_NEB_FieldDomains.wide_arguments','AspisR1.NEI_LPi_TowerValues.qm_sub'],
 'wide_mul':['NEI_NEB_WideCalls.multiply'], 'wide_mul_m31':['NEI_NEB_WideCalls.scale']}
def domain(tag):
 return ('Canonical scalar/record input coordinates; explicit checked-to-wrapping profile transport.' if tag in CANONICAL else 'All typed scalar/record inputs; explicit total checked-to-wrapping profile transport.')
def required(tag):
 return ['NEI_ReleaseField.actual_'+tag]+CUTS.get(tag,[])
