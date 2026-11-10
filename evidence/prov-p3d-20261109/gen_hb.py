import sys
sys.path.insert(0,'.')
import ext
P='field.PreparedQm31Multiplier.mul'
ext.build('../prov-p2f-20261109/PRVEq_RPu_FIq_Native01.lean','PRVEq_RPu_FIq_Native01_P3d.lean',
  steps=[('simp',P+'.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call'),('simp',P)])
