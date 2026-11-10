import sys
sys.path.insert(0,'.')
import ext
ext.build('../prov-p2f-20261109/PRVEq_RPv_RawPoseidonExtensionSlice.lean','PRVEq_RPv_RawPoseidonExtensionSlice_P3d.lean',
  steps=[('nonloop','field.P'),('nonloop','field.reduce_u64'),('nonloop','field.M31.reduce_u62')])
ext.build('../prov-p2f-20261109/PRVEq_RPv_Qm31PackBase4Slice.lean','PRVEq_RPv_Qm31PackBase4Slice_P3d.lean',
  steps=[('nonloop',n) for n in ['field.P','field.reduce_u64','field.M31.reduce_u64','field.CM31.new','field.QM31.Insts.CoreCloneClone.clone','field.QM31.Insts.CoreCloneClone','field.QM31.Insts.CoreMarkerCopy','field.QM31.ZERO','field.qm31_pack_base4']])
