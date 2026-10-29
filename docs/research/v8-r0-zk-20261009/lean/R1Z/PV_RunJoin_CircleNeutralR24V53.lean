import R1Z.PV_RunJoin_CircleNeutralR24Word53
import R1Z.PV_RunJoin_CircleNeutralR24Bounds53
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace R1Z.PV_RunJoin_CircleNeutralR24V53
open PV_RunJoin_CircleNeutralShape53
open PV_RunJoin_CircleNeutralR24Word53
def source (c d g h : U32) : Result U64 := do
  let ch ← UScalar.cast .U64 c * UScalar.cast .U64 h
  let dg ← UScalar.cast .U64 d * UScalar.cast .U64 g
  PV_RunJoin_CircleR72Raw52.field.r24_canonical_mul.closure.Insts.CoreOpsFunctionFnTupleU64U64.call ()
    (core.num.U64.wrapping_add ch dg)
theorem complete (c d g h : U32) (hc : Canon c) (hd : Canon d) (hg : Canon g) (hh : Canon h) :
    source c d g h = ok (word (AspisV8R19.PartialProduct.foldOnce (c.val*h.val+d.val*g.val))) := by
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
  rw [mul _ _ c64 h64 (by omega),bind_tc_ok,mul _ _ d64 g64 (by omega),bind_tc_ok,
    add,PV_RunJoin_CircleNeutralR24Leaf53.fold_call,fold _ (by omega)]

#print axioms source
#print axioms complete
end R1Z.PV_RunJoin_CircleNeutralR24V53
