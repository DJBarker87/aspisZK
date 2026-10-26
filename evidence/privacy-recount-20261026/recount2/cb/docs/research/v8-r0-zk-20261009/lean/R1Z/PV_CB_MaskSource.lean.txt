import R1Z.ProverRwP7CurrentFieldSource
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_CB_MaskSource
open Aeneas Aeneas.Std Result ControlFlow Error
-- Prepared control rebind. Fresh current-source extraction comparison is pending.
def state_only_hiding.mask_power_26
  (value : ProverRwP7CurrentFieldSource.aspis_core.field.QM31) : Result ProverRwP7CurrentFieldSource.aspis_core.field.QM31 := do
  let x2 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square value
  let x4 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square x2
  let x8 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square x4
  let x16 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.square x8
  let q ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul x16 x8
  ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul q x2

def state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS : Std.Usize := 10#usize

def state_only_hiding.selected_mask_linears_loop.body
  (point : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 10#usize)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (suffix : ProverRwP7CurrentFieldSource.aspis_core.field.QM31) (weighted : ProverRwP7CurrentFieldSource.aspis_core.field.QM31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × ProverRwP7CurrentFieldSource.aspis_core.field.QM31 × ProverRwP7CurrentFieldSource.aspis_core.field.QM31) (ProverRwP7CurrentFieldSource.aspis_core.field.QM31 × ProverRwP7CurrentFieldSource.aspis_core.field.QM31))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done (suffix, weighted))
  | some variable1 =>
    let q ← Array.index_usize point variable1
    let suffix1 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add suffix q
    if variable1 != 0#usize
    then
      let weighted1 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add weighted suffix1
      ok (cont (iter1, suffix1, weighted1))
    else ok (cont (iter1, suffix1, weighted))

def state_only_hiding.selected_mask_linears_loop
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (point : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 10#usize) (suffix : ProverRwP7CurrentFieldSource.aspis_core.field.QM31)
  (weighted : ProverRwP7CurrentFieldSource.aspis_core.field.QM31) :
  Result (ProverRwP7CurrentFieldSource.aspis_core.field.QM31 × ProverRwP7CurrentFieldSource.aspis_core.field.QM31)
  := do
  loop
    (fun (iter1, suffix1, weighted1) =>
      state_only_hiding.selected_mask_linears_loop.body point iter1 suffix1
      weighted1)
    (iter, suffix, weighted)

def state_only_hiding.selected_mask_linears
  (point : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 10#usize) : Result (ProverRwP7CurrentFieldSource.aspis_core.field.QM31 × ProverRwP7CurrentFieldSource.aspis_core.field.QM31) := do
  let iter ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize)
      {
        start := 0#usize,
        «end» := state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS
      }
  let (suffix, weighted) ←
    state_only_hiding.selected_mask_linears_loop iter point ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
      ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
  let q ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31 suffix 3#u32
  let q1 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31 weighted 22#u32
  let q2 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add q q1
  let q3 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31 suffix 275#u32
  let q4 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul_m31 weighted 150#u32
  let q5 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add q3 q4
  ok (q2, q5)

def state_only_hiding.cm31_mul_r (value : ProverRwP7CurrentFieldSource.aspis_core.field.CM31) : Result ProverRwP7CurrentFieldSource.aspis_core.field.CM31 := do
  let m ← ProverRwP7CurrentFieldSource.aspis_core.field.M31.double value.a
  let m1 ← ProverRwP7CurrentFieldSource.aspis_core.field.M31.sub m value.b
  let m2 ← ProverRwP7CurrentFieldSource.aspis_core.field.M31.double value.b
  let m3 ← ProverRwP7CurrentFieldSource.aspis_core.field.M31.add value.a m2
  ProverRwP7CurrentFieldSource.aspis_core.field.CM31.new m1 m3

def state_only_hiding.cm31_mul_i (value : ProverRwP7CurrentFieldSource.aspis_core.field.CM31) : Result ProverRwP7CurrentFieldSource.aspis_core.field.CM31 := do
  let m ← ProverRwP7CurrentFieldSource.aspis_core.field.M31.neg value.b
  ProverRwP7CurrentFieldSource.aspis_core.field.CM31.new m value.a

def state_only_hiding.mul_tower_basis
  (value : ProverRwP7CurrentFieldSource.aspis_core.field.QM31) (coordinate : Std.Usize) : Result ProverRwP7CurrentFieldSource.aspis_core.field.QM31 := do
  match coordinate.val with
  | 0 => ok value
  | 1 =>
    let c ← state_only_hiding.cm31_mul_i value.c0
    let c1 ← state_only_hiding.cm31_mul_i value.c1
    ok { c0 := c, c1 }
  | 2 =>
    let c ← state_only_hiding.cm31_mul_r value.c1
    ok { c0 := c, c1 := value.c0 }
  | 3 =>
    let c ← state_only_hiding.cm31_mul_r value.c1
    let c1 ← state_only_hiding.cm31_mul_i c
    let c2 ← state_only_hiding.cm31_mul_i value.c0
    ok { c0 := c1, c1 := c2 }
  | _ => fail panic

def state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS : Array Std.U8 10#usize :=
  Array.make 10#usize [
    1#u8, 3#u8, 5#u8, 7#u8, 9#u8, 11#u8, 15#u8, 17#u8, 19#u8, 21#u8
    ]

def state_only_hiding.FACTOR_EXPONENTS : Array Std.U8 16#usize :=
  Array.make 16#usize [
    0#u8, 2#u8, 4#u8, 6#u8, 8#u8, 10#u8, 12#u8, 14#u8, 16#u8, 18#u8, 20#u8,
    22#u8, 24#u8, 26#u8, 13#u8, 25#u8
    ]

def state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE : Std.Usize := 26#usize

def state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS : Std.Usize :=
  10#usize

def state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS : Std.Usize := 16#usize

def state_only_hiding.state_only_selected_mask_value_loop0.body
  (c1 : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 16#usize) (iter : core.ops.range.Range Std.Usize)
  (coefficients : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31
    27#usize)) (Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done coefficients)
  | some column =>
    let q ← Array.index_usize c1 column
    let i ← lift (column &&& 3#usize)
    let q1 ← state_only_hiding.mul_tower_basis q i
    let i1 ← Array.index_usize state_only_hiding.FACTOR_EXPONENTS column
    let i2 ← lift (core.convert.num.FromUsizeU8.from i1)
    let a ← Array.update coefficients i2 q1
    ok (cont (iter1, a))

def state_only_hiding.state_only_selected_mask_value_loop0
  (iter : core.ops.range.Range Std.Usize) (c1 : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 16#usize)
  (coefficients : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize) :
  Result (Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize)
  := do
  loop
    (fun (iter1, coefficients1) =>
      state_only_hiding.state_only_selected_mask_value_loop0.body c1 iter1
      coefficients1)
    (iter, coefficients)

def state_only_hiding.state_only_selected_mask_value_loop1.body
  (mask_only_c1 : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 10#usize)
  (iter : core.ops.range.Range Std.Usize)
  (coefficients : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31
    27#usize)) (Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done coefficients)
  | some column =>
    let q ← Array.index_usize mask_only_c1 column
    let i ← lift (column &&& 3#usize)
    let q1 ← state_only_hiding.mul_tower_basis q i
    let i1 ←
      Array.index_usize state_only_hiding.MASK_ONLY_FACTOR_EXPONENTS column
    let i2 ← lift (core.convert.num.FromUsizeU8.from i1)
    let a ← Array.update coefficients i2 q1
    ok (cont (iter1, a))

def state_only_hiding.state_only_selected_mask_value_loop1
  (iter : core.ops.range.Range Std.Usize)
  (mask_only_c1 : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 10#usize)
  (coefficients : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize) :
  Result (Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize)
  := do
  loop
    (fun (iter1, coefficients1) =>
      state_only_hiding.state_only_selected_mask_value_loop1.body mask_only_c1
      iter1 coefficients1)
    (iter, coefficients)

def state_only_hiding.state_only_selected_mask_value_loop2.body
  (coefficients : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize)
  (prepared_linear : ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (shared : ProverRwP7CurrentFieldSource.aspis_core.field.QM31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × ProverRwP7CurrentFieldSource.aspis_core.field.QM31) ProverRwP7CurrentFieldSource.aspis_core.field.QM31)
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done shared)
  | some exponent =>
    let q ← ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.mul prepared_linear shared
    let q1 ← Array.index_usize coefficients exponent
    let shared1 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add q q1
    ok (cont (iter1, shared1))

def state_only_hiding.state_only_selected_mask_value_loop2
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (coefficients : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 27#usize)
  (prepared_linear : ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier) (shared : ProverRwP7CurrentFieldSource.aspis_core.field.QM31) :
  Result ProverRwP7CurrentFieldSource.aspis_core.field.QM31
  := do
  loop
    (fun (iter1, shared1) =>
      state_only_hiding.state_only_selected_mask_value_loop2.body coefficients
      prepared_linear iter1 shared1)
    (iter, shared)

def state_only_hiding.state_only_selected_mask_value
  (c1 : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 16#usize) (mask_only_c1 : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 10#usize)
  (explicit_g : ProverRwP7CurrentFieldSource.aspis_core.field.QM31) (point : Array ProverRwP7CurrentFieldSource.aspis_core.field.QM31 10#usize) :
  Result ProverRwP7CurrentFieldSource.aspis_core.field.QM31
  := do
  let (linear, explicit_linear) ←
    state_only_hiding.selected_mask_linears point
  let coefficients := Array.repeat 27#usize ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ZERO
  let coefficients1 ←
    state_only_hiding.state_only_selected_mask_value_loop0
      {
        start := 0#usize,
        «end» := state_only_hiding.STATE_ONLY_HIDING_C1_COLUMNS
      } c1 coefficients
  let coefficients2 ←
    state_only_hiding.state_only_selected_mask_value_loop1
      {
        start := 0#usize,
        «end» := state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS
      } mask_only_c1 coefficients1
  let prepared_linear ← ProverRwP7CurrentFieldSource.aspis_core.field.PreparedQm31Multiplier.new linear
  let shared ←
    Array.index_usize coefficients2
      state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE
  let iter ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize)
      {
        start := 0#usize,
        «end» := state_only_hiding.STATE_ONLY_HIDING_FACTOR_DEGREE
      }
  let shared1 ←
    state_only_hiding.state_only_selected_mask_value_loop2 iter coefficients2
      prepared_linear shared
  let q ← state_only_hiding.mask_power_26 explicit_linear
  let q1 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add ProverRwP7CurrentFieldSource.aspis_core.field.QM31.ONE q
  let q2 ← ProverRwP7CurrentFieldSource.aspis_core.field.QM31.mul q1 explicit_g
  ProverRwP7CurrentFieldSource.aspis_core.field.QM31.add shared1 q2
#print axioms state_only_hiding.state_only_selected_mask_value
end R1Z.PV_CB_MaskSource
