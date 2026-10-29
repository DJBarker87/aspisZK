from pathlib import Path
import importlib.util
T=Path(__file__).parent
sp=importlib.util.spec_from_file_location('w',T/'write-module.py');w=importlib.util.module_from_spec(sp);sp.loader.exec_module(w)
for tag in ['U','V']:
 body='''open PV_RunJoin_CircleNeutralShape53
open PV_RunJoin_CircleNeutralR24Word53
'''
 if tag=='U':
  code='''  let cg ← UScalar.cast .U64 c * UScalar.cast .U64 g
  let pp ← PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.PP
  let dh ← UScalar.cast .U64 d * UScalar.cast .U64 h
  PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call ()
    (core.num.U64.wrapping_sub (core.num.U64.wrapping_add cg pp) dh)
'''
  expr='c.val*g.val+4611686014132420609-d.val*h.val'
 else:
  code='''  let ch ← UScalar.cast .U64 c * UScalar.cast .U64 h
  let dg ← UScalar.cast .U64 d * UScalar.cast .U64 g
  PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call ()
    (core.num.U64.wrapping_add ch dg)
'''
  expr='c.val*h.val+d.val*g.val'
 body+='def source (c d g h : U32) : Result U64 := do\n'+code
 body+=f'''theorem complete (c d g h : U32) (hc : Canon c) (hd : Canon d) (hg : Canon g) (hh : Canon h) :
    source c d g h = ok (word (AspisV8R19.PartialProduct.foldOnce ({expr}))) := by
  have hcg := PV_RunJoin_CircleNeutralR24Bounds53.product c g hc hg
  have hdh := PV_RunJoin_CircleNeutralR24Bounds53.product d h hd hh
  have hch := PV_RunJoin_CircleNeutralR24Bounds53.product c h hc hh
  have hdg := PV_RunJoin_CircleNeutralR24Bounds53.product d g hd hg
  have hbound := PV_RunJoin_CircleNeutralR24Bounds53.intermediate _ _ _ _ hcg hdh hch hdg
  have c64 : c.val < 18446744073709551616 := by have t := c.hBounds;change c.val<4294967296 at t;omega
  have d64 : d.val < 18446744073709551616 := by have t := d.hBounds;change d.val<4294967296 at t;omega
  have g64 : g.val < 18446744073709551616 := by have t := g.hBounds;change g.val<4294967296 at t;omega
  have h64 : h.val < 18446744073709551616 := by have t := h.hBounds;change h.val<4294967296 at t;omega
  unfold source
  rw [widen c,widen d,widen g,widen h]
'''
 if tag=='U':
  body+='''  rw [mul _ _ c64 g64 (by omega),bind_tc_ok,PV_RunJoin_CircleNeutralR24Leaf53.pp,bind_tc_ok,
    mul _ _ d64 h64 (by omega),bind_tc_ok]
  have hp : PV_RunJoin_CircleNeutralR24Leaf53.square = word 4611686014132420609 := by
    apply UScalar.eq_of_val_eq
    rw [PV_RunJoin_CircleNeutralR24Leaf53.square_val,value _ (by decide)]
  rw [hp,add,sub _ _ (by omega) hbound.1,PV_RunJoin_CircleNeutralR24Leaf53.fold_call,
    fold _ (by omega)]
'''
 else:
  body+='''  rw [mul _ _ c64 h64 (by omega),bind_tc_ok,mul _ _ d64 g64 (by omega),bind_tc_ok,
    add,PV_RunJoin_CircleNeutralR24Leaf53.fold_call,fold _ (by omega)]
'''
 w.write('PV_RunJoin_CircleNeutralR24'+tag+'53',['R1Z.PV_RunJoin_CircleNeutralR24Word53','R1Z.PV_RunJoin_CircleNeutralR24Bounds53'],body,['source','complete'])
