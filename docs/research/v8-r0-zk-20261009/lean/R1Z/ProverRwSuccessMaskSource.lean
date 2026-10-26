import R1Z.ProverRwSuccessHeapInstall
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessMaskSource
open Aeneas Aeneas.Std Result ControlFlow Error
abbrev field.M31 := ProverRwFull.aspis_core.field.M31
abbrev field.CM31 := ProverRwFull.aspis_core.field.CM31
abbrev field.QM31 := ProverRwFull.aspis_core.field.QM31
abbrev field.PreparedQm31Multiplier.mul.closure := Unit
structure field.PreparedQm31Multiplier where
  components : Array (Array field.M31 3#usize) 3#usize
abbrev field.PreparedQm31Multiplier.new.closure := Unit
def field.P : Std.U32 := 2147483647#u32

def field.M31.add (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let s ← self + rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

def field.M31.double (self : field.M31) : Result field.M31 := do
  field.M31.add self self

def field.M31.sub (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← self + field.P
  let s ← i - rhs
  if s >= field.P
  then let s1 ← s - field.P
       ok s1
  else ok s

def field.mul_by_r (x : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double x.a
  let m1 ← field.M31.sub m x.b
  let m2 ← field.M31.double x.b
  let m3 ← field.M31.add x.a m2
  ok { a := m1, b := m3 }

def field.CM31.add
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.add self.a rhs.a
  let m1 ← field.M31.add self.b rhs.b
  ok { a := m, b := m1 }

def field.CM31.double (self : field.CM31) : Result field.CM31 := do
  field.CM31.add self self

def field.reduce_u64 (x : Std.U64) : Result Std.U32 := do
  let i ← lift (UScalar.cast .U64 field.P)
  let i1 ← lift (x &&& i)
  let i2 ← x >>> 31#u32
  let x1 ← i1 + i2
  let i3 ← lift (UScalar.cast .U64 field.P)
  let i4 ← lift (x1 &&& i3)
  let i5 ← x1 >>> 31#u32
  let x2 ← i4 + i5
  let x3 ← lift (UScalar.cast .U32 x2)
  if x3 >= field.P
  then x3 - field.P
  else ok x3

def field.M31.reduce_u64 (value : Std.U64) : Result field.M31 := do
  let i ← field.reduce_u64 value
  ok i

def field.M31.mul (self : field.M31) (rhs : field.M31) : Result field.M31 := do
  let i ← lift (UScalar.cast .U64 self)
  let i1 ← lift (UScalar.cast .U64 rhs)
  let i2 ← i * i1
  let i3 ← field.reduce_u64 i2
  ok i3

def field.CM31.square (self : field.CM31) : Result field.CM31 := do
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 ← lift (core.convert.num.FromU64U32.from i)
  let i6 ← lift (core.convert.num.FromU64U32.from field.P)
  let i7 ← i5 + i6
  let i8 ← lift (core.convert.num.FromU64U32.from i2)
  let i9 ← i7 - i8
  let i10 ← i4 * i9
  let m ← field.M31.reduce_u64 i10
  let m1 ← field.M31.mul self.a self.b
  let m2 ← field.M31.double m1
  ok { a := m, b := m2 }

def field.CM31.mul
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m0 ← field.M31.mul self.a rhs.a
  let m1 ← field.M31.mul self.b rhs.b
  let i := self.a
  let i1 ← lift (core.convert.num.FromU64U32.from i)
  let i2 := self.b
  let i3 ← lift (core.convert.num.FromU64U32.from i2)
  let i4 ← i1 + i3
  let i5 := rhs.a
  let i6 ← lift (core.convert.num.FromU64U32.from i5)
  let i7 := rhs.b
  let i8 ← lift (core.convert.num.FromU64U32.from i7)
  let i9 ← i6 + i8
  let i10 ← i4 * i9
  let m2 ← field.M31.reduce_u64 i10
  let m ← field.M31.sub m0 m1
  let m3 ← field.M31.sub m2 m0
  let m4 ← field.M31.sub m3 m1
  ok { a := m, b := m4 }

def field.QM31.square (self : field.QM31) : Result field.QM31 := do
  let c0_square ← field.CM31.square self.c0
  let c1_square ← field.CM31.square self.c1
  let c ← field.mul_by_r c1_square
  let c1 ← field.CM31.add c0_square c
  let c2 ← field.CM31.mul self.c0 self.c1
  let c3 ← field.CM31.double c2
  ok { c0 := c1, c1 := c3 }

def field.CM31.sub
  (self : field.CM31) (rhs : field.CM31) : Result field.CM31 := do
  let m ← field.M31.sub self.a rhs.a
  let m1 ← field.M31.sub self.b rhs.b
  ok { a := m, b := m1 }

def field.QM31.mul
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let m0 ← field.CM31.mul self.c0 rhs.c0
  let m1 ← field.CM31.mul self.c1 rhs.c1
  let c ← field.CM31.add self.c0 self.c1
  let c1 ← field.CM31.add rhs.c0 rhs.c1
  let m2 ← field.CM31.mul c c1
  let c2 ← field.mul_by_r m1
  let c3 ← field.CM31.add m0 c2
  let c4 ← field.CM31.sub m2 m0
  let c5 ← field.CM31.sub c4 m1
  ok { c0 := c3, c1 := c5 }

def state_only_hiding.mask_power_26
  (value : field.QM31) : Result field.QM31 := do
  let x2 ← field.QM31.square value
  let x4 ← field.QM31.square x2
  let x8 ← field.QM31.square x4
  let x16 ← field.QM31.square x8
  let q ← field.QM31.mul x16 x8
  field.QM31.mul q x2

def state_only_hiding.STATE_ONLY_HIDING_SUMCHECK_ROUNDS : Std.Usize := 10#usize

def field.CM31.mul_m31
  (self : field.CM31) (rhs : field.M31) : Result field.CM31 := do
  let m ← field.M31.mul self.a rhs
  let m1 ← field.M31.mul self.b rhs
  ok { a := m, b := m1 }

def field.QM31.mul_m31
  (self : field.QM31) (rhs : field.M31) : Result field.QM31 := do
  let c ← field.CM31.mul_m31 self.c0 rhs
  let c1 ← field.CM31.mul_m31 self.c1 rhs
  ok { c0 := c, c1 }

def field.QM31.add
  (self : field.QM31) (rhs : field.QM31) : Result field.QM31 := do
  let c ← field.CM31.add self.c0 rhs.c0
  let c1 ← field.CM31.add self.c1 rhs.c1
  ok { c0 := c, c1 }

def field.QM31.ZERO : field.QM31 :=
  { c0 := { a := 0#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

def state_only_hiding.selected_mask_linears_loop.body
  (point : Array field.QM31 10#usize)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (suffix : field.QM31) (weighted : field.QM31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × field.QM31 × field.QM31) (field.QM31 × field.QM31))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done (suffix, weighted))
  | some variable1 =>
    let q ← Array.index_usize point variable1
    let suffix1 ← field.QM31.add suffix q
    if variable1 != 0#usize
    then
      let weighted1 ← field.QM31.add weighted suffix1
      ok (cont (iter1, suffix1, weighted1))
    else ok (cont (iter1, suffix1, weighted))

def state_only_hiding.selected_mask_linears_loop
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (point : Array field.QM31 10#usize) (suffix : field.QM31)
  (weighted : field.QM31) :
  Result (field.QM31 × field.QM31)
  := do
  loop
    (fun (iter1, suffix1, weighted1) =>
      state_only_hiding.selected_mask_linears_loop.body point iter1 suffix1
      weighted1)
    (iter, suffix, weighted)

def state_only_hiding.selected_mask_linears
  (point : Array field.QM31 10#usize) : Result (field.QM31 × field.QM31) := do
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
    state_only_hiding.selected_mask_linears_loop iter point field.QM31.ZERO
      field.QM31.ZERO
  let q ← field.QM31.mul_m31 suffix 3#u32
  let q1 ← field.QM31.mul_m31 weighted 22#u32
  let q2 ← field.QM31.add q q1
  let q3 ← field.QM31.mul_m31 suffix 275#u32
  let q4 ← field.QM31.mul_m31 weighted 150#u32
  let q5 ← field.QM31.add q3 q4
  ok (q2, q5)

def field.CM31.new (a : field.M31) (b : field.M31) : Result field.CM31 := do
  ok { a, b }

def state_only_hiding.cm31_mul_r (value : field.CM31) : Result field.CM31 := do
  let m ← field.M31.double value.a
  let m1 ← field.M31.sub m value.b
  let m2 ← field.M31.double value.b
  let m3 ← field.M31.add value.a m2
  field.CM31.new m1 m3

def field.M31.neg (self : field.M31) : Result field.M31 := do
  if self = 0#u32
  then ok 0#u32
  else let i ← field.P - self
       ok i

def state_only_hiding.cm31_mul_i (value : field.CM31) : Result field.CM31 := do
  let m ← field.M31.neg value.b
  field.CM31.new m value.a

def state_only_hiding.mul_tower_basis
  (value : field.QM31) (coordinate : Std.Usize) : Result field.QM31 := do
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

def field.QM31.ONE : field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }

def
  field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
  (c : field.PreparedQm31Multiplier.mul.closure)
  (tupled_args : ((Array field.M31 3#usize) × field.CM31)) :
  Result field.CM31
  := do
  let (left, right) := tupled_args
  let m ← Array.index_usize left 0#usize
  let m0 ← field.M31.mul m right.a
  let m1 ← Array.index_usize left 1#usize
  let m11 ← field.M31.mul m1 right.b
  let m2 ← Array.index_usize left 2#usize
  let m3 ← field.M31.add right.a right.b
  let m21 ← field.M31.mul m2 m3
  let m4 ← field.M31.sub m0 m11
  let m5 ← field.M31.sub m21 m0
  let m6 ← field.M31.sub m5 m11
  ok { a := m4, b := m6 }

def field.PreparedQm31Multiplier.mul
  (self : field.PreparedQm31Multiplier) (rhs : field.QM31) :
  Result field.QM31
  := do
  let a ← Array.index_usize self.components 0#usize
  let m0 ←
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a, rhs.c0)
  let a1 ← Array.index_usize self.components 1#usize
  let m1 ←
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a1, rhs.c1)
  let a2 ← Array.index_usize self.components 2#usize
  let c ← field.CM31.add rhs.c0 rhs.c1
  let m2 ←
    field.PreparedQm31Multiplier.mul.closure.Insts.CoreOpsFunctionFnPairArrayM313CM31CM31.call
      () (a2, c)
  let c1 ← field.mul_by_r m1
  let c2 ← field.CM31.add m0 c1
  let c3 ← field.CM31.sub m2 m0
  let c4 ← field.CM31.sub c3 m1
  ok { c0 := c2, c1 := c4 }

def
  field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
  (c : field.PreparedQm31Multiplier.new.closure) (tupled_args : field.CM31) :
  Result (Array field.M31 3#usize)
  := do
  let m ← field.M31.add tupled_args.a tupled_args.b
  ok (Array.make 3#usize [ tupled_args.a, tupled_args.b, m ])

def field.PreparedQm31Multiplier.new
  (value : field.QM31) : Result field.PreparedQm31Multiplier := do
  let a ←
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () value.c0
  let a1 ←
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () value.c1
  let c ← field.CM31.add value.c0 value.c1
  let a2 ←
    field.PreparedQm31Multiplier.new.closure.Insts.CoreOpsFunctionFnTupleCM31ArrayM313.call
      () c
  ok { components := (Array.make 3#usize [ a, a1, a2 ]) }

def state_only_hiding.state_only_selected_mask_value_loop0.body
  (c1 : Array field.QM31 16#usize) (iter : core.ops.range.Range Std.Usize)
  (coefficients : Array field.QM31 27#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array field.QM31
    27#usize)) (Array field.QM31 27#usize))
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
  (iter : core.ops.range.Range Std.Usize) (c1 : Array field.QM31 16#usize)
  (coefficients : Array field.QM31 27#usize) :
  Result (Array field.QM31 27#usize)
  := do
  loop
    (fun (iter1, coefficients1) =>
      state_only_hiding.state_only_selected_mask_value_loop0.body c1 iter1
      coefficients1)
    (iter, coefficients)

def state_only_hiding.state_only_selected_mask_value_loop1.body
  (mask_only_c1 : Array field.QM31 10#usize)
  (iter : core.ops.range.Range Std.Usize)
  (coefficients : Array field.QM31 27#usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Array field.QM31
    27#usize)) (Array field.QM31 27#usize))
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
  (mask_only_c1 : Array field.QM31 10#usize)
  (coefficients : Array field.QM31 27#usize) :
  Result (Array field.QM31 27#usize)
  := do
  loop
    (fun (iter1, coefficients1) =>
      state_only_hiding.state_only_selected_mask_value_loop1.body mask_only_c1
      iter1 coefficients1)
    (iter, coefficients)

def state_only_hiding.state_only_selected_mask_value_loop2.body
  (coefficients : Array field.QM31 27#usize)
  (prepared_linear : field.PreparedQm31Multiplier)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (shared : field.QM31) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × field.QM31) field.QM31)
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done shared)
  | some exponent =>
    let q ← field.PreparedQm31Multiplier.mul prepared_linear shared
    let q1 ← Array.index_usize coefficients exponent
    let shared1 ← field.QM31.add q q1
    ok (cont (iter1, shared1))

def state_only_hiding.state_only_selected_mask_value_loop2
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (coefficients : Array field.QM31 27#usize)
  (prepared_linear : field.PreparedQm31Multiplier) (shared : field.QM31) :
  Result field.QM31
  := do
  loop
    (fun (iter1, shared1) =>
      state_only_hiding.state_only_selected_mask_value_loop2.body coefficients
      prepared_linear iter1 shared1)
    (iter, shared)

def state_only_hiding.state_only_selected_mask_value
  (c1 : Array field.QM31 16#usize) (mask_only_c1 : Array field.QM31 10#usize)
  (explicit_g : field.QM31) (point : Array field.QM31 10#usize) :
  Result field.QM31
  := do
  let (linear, explicit_linear) ←
    state_only_hiding.selected_mask_linears point
  let coefficients := Array.repeat 27#usize field.QM31.ZERO
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
  let prepared_linear ← field.PreparedQm31Multiplier.new linear
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
  let q1 ← field.QM31.add field.QM31.ONE q
  let q2 ← field.QM31.mul q1 explicit_g
  field.QM31.add shared1 q2
end R1Z.ProverRwSuccessMaskSource
