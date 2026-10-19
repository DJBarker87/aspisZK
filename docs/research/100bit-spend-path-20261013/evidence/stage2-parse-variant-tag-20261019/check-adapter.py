from pathlib import Path
import re
p=Path(__file__).resolve().parent
raw_root=p/'extraction'
clean=lambda t:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',t,flags=re.M)
class Raw:
 def __truediv__(self,n):return raw_root/('generated-'+n)
b=Raw()
t=clean((b/'Funs.lean').read_text()).replace('import AspisR1Stage2AdoptedParseShape.FunsExternal\n','');struct='''
structure ParseShapeOps where
  sliceEq : {T U : Type} → {n : Usize} → core.cmp.PartialEq T U → Slice T → Array U n → Result Bool
  sliceNe : {T U : Type} → {n : Usize} → core.cmp.PartialEq T U → Slice T → Array U n → Result Bool
  iterAny : {T F : Type} → core.ops.function.FnMut F T Bool → core.slice.iter.Iter T → F → Result (Bool × core.slice.iter.Iter T)
'''
t=t.replace('namespace AspisR1Stage2AdoptedParseShape\n','namespace AspisR1Stage2AdoptedParseShape\n'+struct,1).replace('def Slice.Insts.CoreCmpPartialEqArray {T : Type}','def Slice.Insts.CoreCmpPartialEqArray (ops : ParseShapeOps) {T : Type}').replace('eq := Slice.Insts.CoreCmpPartialEqArray.eq cmpPartialEqInst','eq := ops.sliceEq cmpPartialEqInst').replace('ne := Slice.Insts.CoreCmpPartialEqArray.ne cmpPartialEqInst','ne := ops.sliceNe cmpPartialEqInst').replace('def verifier.candidate.parse_shape\n','def verifier.candidate.parse_shape\n  (ops : ParseShapeOps)\n').replace('(Slice.Insts.CoreCmpPartialEqArray\n        8#usize','(Slice.Insts.CoreCmpPartialEqArray ops\n        8#usize').replace('core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any\n','ops.iterAny\n')
assert t==(p/'sources/Stage2ParseShapeExplicitOps.lean').read_text()
assert clean((b/'Types.lean').read_text())==(p/'sources/AspisR1Stage2AdoptedParseShape/Types.lean').read_text()
print('Checked generated parser preservation under explicit operations; resource settings removed')
