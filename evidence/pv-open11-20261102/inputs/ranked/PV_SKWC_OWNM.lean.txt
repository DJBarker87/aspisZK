import R1Z.PV_B2_W_16_QM31_ONE
import R1Z.PV_B2_Total_QM31_ZERO
import R1Z.PV_B2_W_17_QM31_add
import R1Z.PV_B2_W_18_QM31_sub
import R1Z.PV_B2_W_19_QM31_mul
import R1Z.PV_RDB2D_CollectorTrace
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Aeneas
import AspisV8R15.ExactTowerBase
import Mathlib.Tactic.Ring
import R1Z.PV_OWNM_V239
import PV_SKW_DIAG_FILE
import PV_SKW_DIAG_JSON_STDOUT
import PV_SKW_DIAG_ERROR_STDERR
import PV_SKW_L1

section
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.QM31.ONE : aspis_core.field.QM31 :=
  { c0 := { a := 1#u32, b := 0#u32 }, c1 := { a := 0#u32, b := 0#u32 } }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_ONE : PV_B2_WeightsNative.aspis_core.field.QM31.ONE = PV_B2_FieldValue.aspis_core.field.QM31.ONE := by
  unfold PV_B2_WeightsNative.aspis_core.field.QM31.ONE PV_B2_FieldValue.aspis_core.field.QM31.ONE
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub, PV_B2_FieldTotal.CM31_sub, PV_B2_FieldTotal.CM31_mul, PV_B2_FieldTotal.mul_by_r, PV_B2_FieldTotal.QM31_ZERO,lift,bind_tc_ok]
#print axioms QM31_ONE
end PV_B2_FieldTotal

end

section
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.QM31.add
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  aspis_core.field.QM31
  :=
  let c := aspis_core.field.CM31.add self.c0 rhs.c0
  let c1 := aspis_core.field.CM31.add self.c1 rhs.c1
  { c0 := c, c1 }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_add (self : ProverRwFull.aspis_core.field.QM31) (rhs : ProverRwFull.aspis_core.field.QM31) : PV_B2_WeightsNative.aspis_core.field.QM31.add self rhs = ok (PV_B2_FieldValue.aspis_core.field.QM31.add self rhs) := by
  unfold PV_B2_WeightsNative.aspis_core.field.QM31.add PV_B2_FieldValue.aspis_core.field.QM31.add
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub, PV_B2_FieldTotal.CM31_sub, PV_B2_FieldTotal.CM31_mul, PV_B2_FieldTotal.mul_by_r, PV_B2_FieldTotal.QM31_ZERO, PV_B2_FieldTotal.QM31_ONE,lift,bind_tc_ok]
#print axioms QM31_add
end PV_B2_FieldTotal

end

section
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.QM31.sub
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  aspis_core.field.QM31
  :=
  let c := aspis_core.field.CM31.sub self.c0 rhs.c0
  let c1 := aspis_core.field.CM31.sub self.c1 rhs.c1
  { c0 := c, c1 }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_sub (self : ProverRwFull.aspis_core.field.QM31) (rhs : ProverRwFull.aspis_core.field.QM31) : PV_B2_WeightsNative.aspis_core.field.QM31.sub self rhs = ok (PV_B2_FieldValue.aspis_core.field.QM31.sub self rhs) := by
  unfold PV_B2_WeightsNative.aspis_core.field.QM31.sub PV_B2_FieldValue.aspis_core.field.QM31.sub
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub, PV_B2_FieldTotal.CM31_sub, PV_B2_FieldTotal.CM31_mul, PV_B2_FieldTotal.mul_by_r, PV_B2_FieldTotal.QM31_ZERO, PV_B2_FieldTotal.QM31_ONE, PV_B2_FieldTotal.QM31_add,lift,bind_tc_ok]
#print axioms QM31_sub
end PV_B2_FieldTotal

end

section
open Aeneas Aeneas.Std Result
namespace PV_B2_FieldValue
def aspis_core.field.QM31.mul
  (self : aspis_core.field.QM31) (rhs : aspis_core.field.QM31) :
  aspis_core.field.QM31
  :=
  let m0 := aspis_core.field.CM31.mul self.c0 rhs.c0
  let m1 := aspis_core.field.CM31.mul self.c1 rhs.c1
  let c := aspis_core.field.CM31.add self.c0 self.c1
  let c1 := aspis_core.field.CM31.add rhs.c0 rhs.c1
  let m2 := aspis_core.field.CM31.mul c c1
  let c2 := aspis_core.field.mul_by_r m1
  let c3 := aspis_core.field.CM31.add m0 c2
  let c4 := aspis_core.field.CM31.sub m2 m0
  let c5 := aspis_core.field.CM31.sub c4 m1
  { c0 := c3, c1 := c5 }
end PV_B2_FieldValue
namespace PV_B2_FieldTotal
/-- Full Result, arbitrary raw inputs; shared symbolic operations avoid field-term reduction. -/
theorem QM31_mul (self : ProverRwFull.aspis_core.field.QM31) (rhs : ProverRwFull.aspis_core.field.QM31) : PV_B2_WeightsNative.aspis_core.field.QM31.mul self rhs = ok (PV_B2_FieldValue.aspis_core.field.QM31.mul self rhs) := by
  unfold PV_B2_WeightsNative.aspis_core.field.QM31.mul PV_B2_FieldValue.aspis_core.field.QM31.mul
  simp only [PV_B2_FieldTotal.P, PV_B2_FieldTotal.ct_subtract_p, PV_B2_FieldTotal.ct_reduce64, PV_B2_FieldTotal.ct_add, PV_B2_FieldTotal.ct_sub, PV_B2_FieldTotal.reduce_u64, PV_B2_FieldTotal.M31_mul, PV_B2_FieldTotal.M31_reduce_u64, PV_B2_FieldTotal.M31_add, PV_B2_FieldTotal.M31_double, PV_B2_FieldTotal.CM31_add, PV_B2_FieldTotal.M31_sub, PV_B2_FieldTotal.CM31_sub, PV_B2_FieldTotal.CM31_mul, PV_B2_FieldTotal.mul_by_r, PV_B2_FieldTotal.QM31_ZERO, PV_B2_FieldTotal.QM31_ONE, PV_B2_FieldTotal.QM31_add, PV_B2_FieldTotal.QM31_sub,lift,bind_tc_ok]
#print axioms QM31_mul
end PV_B2_FieldTotal

end

section
namespace R1Z.PV_RDB2D_SparseShape
open Aeneas Aeneas.Std Result
set_option autoImplicit false

/-- The supplied Boolean predicate is the concrete zero/one test. The source
association to raw QM31 equality is separate; no canonicality is assumed here. -/
def trailing {K : Type} (isBoolean : K → Bool) (point : List K) : Nat :=
  (point.reverse.takeWhile isBoolean).length

def prefixLen {K : Type} (isBoolean : K → Bool) (point : List K) : Nat :=
  point.length-trailing isBoolean point

def capacity {K : Type} (isBoolean : K → Bool) (point : List K) : Nat :=
  2^prefixLen isBoolean point

theorem trailing_bound {K : Type} (isBoolean : K → Bool) (point : List K) :
    trailing isBoolean point≤point.length := by
  unfold trailing
  have bound : ∀ xs : List K, (xs.takeWhile isBoolean).length≤xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      cases h : isBoolean x <;> simp [List.takeWhile,h] <;> omega
  exact (bound point.reverse).trans_eq List.length_reverse

theorem split_length {K : Type} (isBoolean : K → Bool) (point : List K) :
    prefixLen isBoolean point+trailing isBoolean point=point.length := by
  have h := trailing_bound isBoolean point
  unfold prefixLen
  omega

theorem capacity_positive {K : Type} (isBoolean : K → Bool) (point : List K) :
    0<capacity isBoolean point := Nat.two_pow_pos _

theorem capacity_bound {K : Type} (isBoolean : K → Bool) (point : List K)
    (length : point.length=10) : capacity isBoolean point≤1024 := by
  have hp : prefixLen isBoolean point≤10 := by unfold prefixLen;omega
  exact Nat.pow_le_pow_right (by omega) hp

theorem same_public_point {K H : Type} (isBoolean : K → Bool) (point : List K) (left right : H) :
    (fun (_ : H) => capacity isBoolean point) left=(fun (_ : H) => capacity isBoolean point) right := rfl

#print axioms trailing_bound
#print axioms split_length
#print axioms capacity_positive
#print axioms capacity_bound
#print axioms same_public_point
end R1Z.PV_RDB2D_SparseShape

end

section
namespace R1Z.PV_RDB2D_SparseAddress
set_option autoImplicit false

def row (pref trailing suffix : Nat) : Nat := pref*2^trailing+suffix

theorem bound (width trailing suffix pref : Nat) (split : width+trailing=10)
    (hs : suffix<2^trailing) (hp : pref<2^width) : row pref trailing suffix<1024 := by
  unfold row
  calc
    pref*2^trailing+suffix < (pref+1)*2^trailing := by
      rw [Nat.add_mul,Nat.one_mul];omega
    _ ≤ 2^width*2^trailing := Nat.mul_le_mul_right _ hp
    _ = 2^10 := by rw [←Nat.pow_add,split]
    _ = 1024 := rfl

theorem injective (trailing suffix a b : Nat) (hs : suffix<2^trailing)
    (h : row a trailing suffix=row b trailing suffix) : a=b := by
  unfold row at h
  have hp := Nat.two_pow_pos trailing
  have eq : a*2^trailing=b*2^trailing := by omega
  exact Nat.eq_of_mul_eq_mul_right hp eq

theorem ordered (trailing suffix a b : Nat) (h : a<b) :
    row a trailing suffix<row b trailing suffix := by
  unfold row
  exact Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos _)) _

theorem quotient (trailing suffix pref : Nat) (hs : suffix<2^trailing) :
    row pref trailing suffix/2^trailing=pref := by
  unfold row
  have hm : (pref*2^trailing+suffix)%2^trailing=suffix := by
    simp [Nat.add_mod,Nat.mod_eq_of_lt hs]
  have hd := Nat.mod_add_div (pref*2^trailing+suffix) (2^trailing)
  rw [hm] at hd
  have eq : pref*2^trailing=2^trailing*((pref*2^trailing+suffix)/2^trailing) := by omega
  rw [Nat.mul_comm (2^trailing)] at eq
  exact (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos trailing) eq).symm


#print axioms bound
#print axioms injective
#print axioms ordered
#print axioms quotient
end R1Z.PV_RDB2D_SparseAddress

end

section
namespace R1Z.PV_RDB2D_SparseLookup
open Aeneas Aeneas.Std Result
set_option autoImplicit false

def read {K : Type} (column : List K) (row : Nat) : Result K :=
  match column[row]? with
  | none => fail .arrayOutOfBounds
  | some value => ok value

theorem present {K : Type} (column : List K) (row : Nat) (h : row<column.length) :
    read column row=ok (column[row]'h) := by
  simp only [read,List.getElem?_eq_getElem h]

theorem absent {K : Type} (column : List K) (row : Nat) (h : column.length≤row) :
    read column row=fail .arrayOutOfBounds := by
  simp only [read,List.getElem?_eq_none h]

theorem sparse_present {K : Type} (column : List K) (length : column.length=1024)
    (width trailing suffix pref : Nat) (split : width+trailing=10)
    (hs : suffix<2^trailing) (hp : pref<2^width) :
    ∃ value, read column (PV_RDB2D_SparseAddress.row pref trailing suffix)=ok value := by
  have h := PV_RDB2D_SparseAddress.bound width trailing suffix pref split hs hp
  have bound : PV_RDB2D_SparseAddress.row pref trailing suffix<column.length := by omega
  exact ⟨column[_]'bound,present column _ bound⟩

#print axioms present
#print axioms absent
#print axioms sparse_present
end R1Z.PV_RDB2D_SparseLookup

end

section
namespace R1Z.PV_RDB2D_SparseFold
open Aeneas Aeneas.Std Result
set_option autoImplicit false

structure Ops (K : Type) where
  zero : K
  mul : K → K → Result K
  add : K → K → Result K
abbrev Entry (K : Type) := Nat × K

def term {K : Type} (ops : Ops K) (column : List K) (acc : K) (entry : Entry K) : Result K := do
  let value ← PV_RDB2D_SparseLookup.read column entry.1
  let product ← ops.mul entry.2 value
  ops.add acc product

def source {K : Type} (ops : Ops K) (column : List K) : List (Entry K) → K → Result K
  | [],acc => ok acc
  | entry::tail,acc => do
    let next ← term ops column acc entry
    source ops column tail next

def reference {K : Type} (ops : Ops K) (column : List K) (entries : List (Entry K)) (acc : K) : Result K :=
  entries.foldlM (term ops column) acc

/-- Arbitrary columns and raw scalar operations: no constant-column fixture,
canonical-field image, assumed result, or commuting/reordered field calls. -/
theorem arbitrary_column {K : Type} (ops : Ops K) (column : List K)
    (entries : List (Entry K)) (acc : K) :
    source ops column entries acc=reference ops column entries acc := by
  induction entries generalizing acc with
  | nil => rfl
  | cons entry tail ih =>
    simp only [source,reference,List.foldlM_cons]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih next

theorem failure_stops_suffix {K : Type} (ops : Ops K) (column : List K)
    (entry : Entry K) (tail : List (Entry K)) (acc : K) (e : Error)
    (h : term ops column acc entry=fail e) : source ops column (entry::tail) acc=fail e := by
  simp only [source,h,bind_tc_fail]

theorem divergence_stops_suffix {K : Type} (ops : Ops K) (column : List K)
    (entry : Entry K) (tail : List (Entry K)) (acc : K)
    (h : term ops column acc entry=div) : source ops column (entry::tail) acc=div := by
  simp only [source,h,bind_tc_div]

#print axioms arbitrary_column
#print axioms failure_stops_suffix
#print axioms divergence_stops_suffix
end R1Z.PV_RDB2D_SparseFold

end

section
namespace R1Z.PV_RDB2D_SparseEntries
open PV_RDB2D_SparseAddress
set_option autoImplicit false

def entries {K : Type} (width trailing suffix : Nat) (weight : Nat → K) : List (Nat × K) :=
  (List.range (2^width)).map (fun pref => (row pref trailing suffix,weight pref))

theorem length {K : Type} (width trailing suffix : Nat) (weight : Nat → K) :
    (entries width trailing suffix weight).length=2^width := by simp only [entries,List.length_map,List.length_range]

theorem rows_bounded {K : Type} (width trailing suffix : Nat) (weight : Nat → K)
    (split : width+trailing=10) (hs : suffix<2^trailing) :
    ∀ entry ∈ entries width trailing suffix weight, entry.1<1024 := by
  intro entry h
  obtain ⟨pref,hp,rfl⟩ := List.mem_map.mp h
  exact bound width trailing suffix pref split hs (List.mem_range.mp hp)

#print axioms length
#print axioms rows_bounded
end R1Z.PV_RDB2D_SparseEntries

end

section
namespace R1Z.PV_RDB2D_SparseWeights
open Aeneas Aeneas.Std Result PV_RDB2D_SparseFold
set_option autoImplicit false
structure WeightOps (K : Type) extends Ops K where
  one : K
  subOne : K → Result K

def step {K : Type} (ops : WeightOps K) (width pref : Nat) (acc : K × Nat) (coordinate : K) : Result (K × Nat) := do
  let factor ← if pref.testBit (width-1-acc.2) then ok coordinate else ops.subOne coordinate
  let weight ← ops.mul acc.1 factor
  ok (weight,acc.2+1)

def source {K : Type} (ops : WeightOps K) (width pref : Nat) : List K → K × Nat → Result (K × Nat)
  | [],acc => ok acc
  | coordinate::tail,acc => do
    let next ← step ops width pref acc coordinate
    source ops width pref tail next

def reference {K : Type} (ops : WeightOps K) (width pref : Nat) (coordinates : List K) (acc : K × Nat) : Result (K × Nat) :=
  coordinates.foldlM (step ops width pref) acc

theorem all_coordinates {K : Type} (ops : WeightOps K) (width pref : Nat)
    (coordinates : List K) (acc : K × Nat) :
    source ops width pref coordinates acc=reference ops width pref coordinates acc := by
  induction coordinates generalizing acc with
  | nil => rfl
  | cons coordinate tail ih =>
    simp only [source,reference,List.foldlM_cons]
    apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
    intro next _
    exact ih next

def build {K : Type} (ops : WeightOps K) (point : List K) (width trailing suffix : Nat) : Result (List (Entry K)) :=
  (List.range (2^width)).mapM fun pref => do
    let (weight,_) ← source ops width pref (point.take width) (ops.one,0)
    ok (PV_RDB2D_SparseAddress.row pref trailing suffix,weight)

#print axioms all_coordinates
end R1Z.PV_RDB2D_SparseWeights

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNI_RawOps
open Aeneas Aeneas.Std Result
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev valueAdd := PV_B2_FieldValue.aspis_core.field.QM31.add
abbrev valueMul := PV_B2_FieldValue.aspis_core.field.QM31.mul
abbrev valueSub := PV_B2_FieldValue.aspis_core.field.QM31.sub
abbrev zero := PV_B2_FieldValue.aspis_core.field.QM31.ZERO
abbrev one := PV_B2_FieldValue.aspis_core.field.QM31.ONE
/-- The actual ordered Result methods, on all four raw u32 limbs. -/
def ops : PV_RDB2D_SparseWeights.WeightOps Q :=
 {zero:=PV_B2_WeightsNative.aspis_core.field.QM31.ZERO
  one:=PV_B2_WeightsNative.aspis_core.field.QM31.ONE
  mul:=PV_B2_WeightsNative.aspis_core.field.QM31.mul
  add:=PV_B2_WeightsNative.aspis_core.field.QM31.add
  subOne:=fun q=>PV_B2_WeightsNative.aspis_core.field.QM31.sub
   PV_B2_WeightsNative.aspis_core.field.QM31.ONE q}

theorem mul (a b : Q) : ops.mul a b=ok (valueMul a b) := PV_B2_FieldTotal.QM31_mul a b
theorem add (a b : Q) : ops.add a b=ok (valueAdd a b) := PV_B2_FieldTotal.QM31_add a b
theorem sub (a : Q) : ops.subOne a=ok (valueSub one a) := by
 change PV_B2_WeightsNative.aspis_core.field.QM31.sub _ _=_
 rw [PV_B2_FieldTotal.QM31_sub,PV_B2_FieldTotal.QM31_ONE]
theorem zero_value : ops.zero=zero := PV_B2_FieldTotal.QM31_ZERO
theorem one_value : ops.one=one := PV_B2_FieldTotal.QM31_ONE
#print axioms mul
#print axioms add
#print axioms sub
#print axioms zero_value
#print axioms one_value
end R1Z.PV_OWNI_RawOps

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNI_WeightTotal
open Aeneas Aeneas.Std Result PV_OWNI_RawOps

def step (width pref : Nat) (acc : Q × Nat) (coordinate : Q) : Q × Nat :=
 (valueMul acc.1 (if pref.testBit (width-1-acc.2) then coordinate else valueSub one coordinate),acc.2+1)

theorem step_result (width pref : Nat) (acc : Q × Nat) (coordinate : Q) :
 PV_RDB2D_SparseWeights.step ops width pref acc coordinate=ok (step width pref acc coordinate) := by
 unfold PV_RDB2D_SparseWeights.step step
 cases h:pref.testBit (width-1-acc.2) <;>
  simp only [h,Bool.false_eq_true,if_false,if_true,sub,mul,bind_tc_ok]

theorem source_result (width pref : Nat) (coordinates : List Q) (acc : Q × Nat) :
 PV_RDB2D_SparseWeights.source ops width pref coordinates acc=
 ok (coordinates.foldl (step width pref) acc) := by
 induction coordinates generalizing acc with
 | nil => rfl
 | cons x xs ih =>
  rw [PV_RDB2D_SparseWeights.source,step_result]
  simp only [bind_tc_ok,List.foldl_cons]
  exact ih _
#print axioms step_result
#print axioms source_result
end R1Z.PV_OWNI_WeightTotal

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNI_MapMLength
open Aeneas Aeneas.Std Result
/-- Successful monadic enumeration preserves count; failures/divergence are
not assumed away by a pure-list replacement. -/
theorem length {A B : Type} (f : A → Result B) (xs : List A) (ys : List B)
 (h:xs.mapM f=ok ys) : ys.length=xs.length := by
 induction xs generalizing ys with
 | nil =>
  have hh : ([] : List B)=ys := by injection h
  subst ys
  rfl
 | cons x xs ih =>
  cases hx:f x with
  | fail e => simp only [List.mapM_cons,hx,bind_tc_fail] at h; cases h
  | div => simp only [List.mapM_cons,hx,bind_tc_div] at h; cases h
  | ok y =>
   cases ht:xs.mapM f with
   | fail e => simp only [List.mapM_cons,hx,ht,bind_tc_ok,bind_tc_fail] at h; cases h
   | div => simp only [List.mapM_cons,hx,ht,bind_tc_ok,bind_tc_div] at h; cases h
   | ok tail =>
    have hh : y::tail=ys := by
     have eq:(ok (y::tail) : Result (List B))=ok ys := by
      simp only [List.mapM_cons,hx,ht,bind_tc_ok] at h
      change ok (y::tail)=ok ys at h
      exact h
     exact Result.ok.inj eq
    subst ys
    rw [List.length_cons,List.length_cons,ih tail ht]
#print axioms length
end R1Z.PV_OWNI_MapMLength

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNI_BuildTotal
open Aeneas Aeneas.Std Result PV_OWNI_RawOps

def entries (point : List Q) (width trailing suffix : Nat) : List (Nat × Q) :=
 (List.range (2^width)).map fun pref=>
 (PV_RDB2D_SparseAddress.row pref trailing suffix,
  ((point.take width).foldl (PV_OWNI_WeightTotal.step width pref) (ops.one,0)).1)

theorem mapM_pure {A B : Type} (xs : List A) (f : A → B) :
 xs.mapM (fun x=>ok (f x))=ok (xs.map f) := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
  simp only [List.mapM_cons,List.map_cons,ih,bind_tc_ok]
  rfl

theorem result (point : List Q) (width trailing suffix : Nat) :
 PV_RDB2D_SparseWeights.build ops point width trailing suffix=ok (entries point width trailing suffix) := by
 unfold PV_RDB2D_SparseWeights.build
 simp only [PV_OWNI_WeightTotal.source_result,bind_tc_ok]
 exact mapM_pure _ _

theorem cardinality (point : List Q) (width trailing suffix : Nat) :
 (entries point width trailing suffix).length=2^width := by
 have h:=PV_OWNI_MapMLength.length _ _ _ (result point width trailing suffix)
 simpa only [List.length_range] using h
#print axioms mapM_pure
#print axioms result
#print axioms cardinality
end R1Z.PV_OWNI_BuildTotal

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNI_Rows
open PV_OWNI_RawOps PV_OWNI_BuildTotal

theorem bounded (point : List Q) (width trailing suffix : Nat)
 (split:width+trailing=10) (hs:suffix<2^trailing) :
 ∀ entry∈entries point width trailing suffix,entry.1<1024 := by
 intro entry he
 obtain ⟨pref,hp,rfl⟩:=List.mem_map.mp he
 exact PV_RDB2D_SparseAddress.bound width trailing suffix pref split hs (List.mem_range.mp hp)

#print axioms bounded
end R1Z.PV_OWNI_Rows

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNI_RawFold
open Aeneas Aeneas.Std Result PV_OWNI_RawOps

def term (column : List Q) (sum : Q) (entry : Nat × Q) : Q :=
 valueAdd sum (valueMul entry.2 (column[entry.1]?.getD zero))

theorem term_result (column : List Q) (sum : Q) (entry : Nat × Q)
 (h:entry.1<column.length) :
 PV_RDB2D_SparseFold.term ops.toOps column sum entry=ok (term column sum entry) := by
 rw [PV_RDB2D_SparseFold.term,PV_RDB2D_SparseLookup.present column entry.1 h]
 simp only [bind_tc_ok,mul,add,term,List.getElem?_eq_getElem h,Option.getD_some]

theorem result (column : List Q) (xs : List (Nat × Q)) (sum : Q)
 (bound:∀ e∈xs,e.1<column.length) :
 PV_RDB2D_SparseFold.source ops.toOps column xs sum=ok (xs.foldl (term column) sum) := by
 induction xs generalizing sum with
 | nil => rfl
 | cons e es ih =>
  rw [PV_RDB2D_SparseFold.source,term_result column sum e (bound e (by simp))]
  simp only [bind_tc_ok,List.foldl_cons]
  exact ih _ (fun x hx=>bound x (by simp only [List.mem_cons];exact Or.inr hx))
#print axioms term_result
#print axioms result
end R1Z.PV_OWNI_RawFold

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNI_RawConsumer
open Aeneas Aeneas.Std Result PV_OWNI_RawOps

def source (point column : List Q) (width trailing suffix : Nat) : Result (Option Q) := do
 if column.length≠1024 then ok none else
  let entries←PV_RDB2D_SparseWeights.build ops point width trailing suffix
  let sum←PV_RDB2D_SparseFold.source ops.toOps column entries ops.zero
  ok (some sum)

def value (point column : List Q) (width trailing suffix : Nat) : Option Q :=
 if column.length≠1024 then none else
 some ((PV_OWNI_BuildTotal.entries point width trailing suffix).foldl
  (PV_OWNI_RawFold.term column) zero)

/-- Complete value-phase Result on arbitrary raw inputs, once the concrete
scanner's split/suffix bounds are supplied. No canonicality or success premise. -/
theorem result (point column : List Q) (width trailing suffix : Nat)
 (split:width+trailing=10) (hs:suffix<2^trailing) :
 source point column width trailing suffix=ok (value point column width trailing suffix) := by
 by_cases h:column.length≠1024
 · unfold source value
   rw [if_pos h,if_pos h]
 · have len:column.length=1024 := by omega
   unfold source value
   simp only [h,if_false,PV_OWNI_BuildTotal.result,bind_tc_ok,zero_value]
   rw [PV_OWNI_RawFold.result]
   · rfl
   · intro e he
     have hb:=PV_OWNI_Rows.bounded point width trailing suffix split hs e he
     omega
#print axioms result
end R1Z.PV_OWNI_RawConsumer

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNI_Scanner
open PV_OWNI_RawOps
/-- Literal raw equality, including all four limbs; never equality modulo P. -/
def equal (a b : Q) : Bool :=
 (a.c0.a.val==b.c0.a.val)&&(a.c0.b.val==b.c0.b.val)&&
 (a.c1.a.val==b.c1.a.val)&&(a.c1.b.val==b.c1.b.val)
def boolean (a : Q) : Bool := equal a zero || equal a one
def width (point : List Q) : Nat := PV_RDB2D_SparseShape.prefixLen boolean point
def trailing (point : List Q) : Nat := PV_RDB2D_SparseShape.trailing boolean point
/-- Big-endian suffix shift/OR. Zero and one are distinguished literally. -/
def bits : List Q → Nat
 | [] => 0
 | x::xs => (if equal x one then 1 else 0)*2^xs.length+bits xs
def suffix (point : List Q) : Nat := bits (point.drop (width point))

theorem bits_bound (xs : List Q) : bits xs<2^xs.length := by
 induction xs with
 | nil => change 0<1;omega
 | cons x xs ih =>
  rw [bits,List.length_cons,Nat.pow_succ]
  cases h:equal x one <;> simp only [h,Bool.false_eq_true,if_false,if_true] <;> omega

theorem split (point : List Q) (len:point.length=10) :
 width point+trailing point=10 := by
 rw [width,trailing,PV_RDB2D_SparseShape.split_length,len]

theorem suffix_bound (point : List Q) : suffix point<2^trailing point := by
 have h:=bits_bound (point.drop (width point))
 have split:=PV_RDB2D_SparseShape.split_length boolean point
 have hp:width point≤point.length := by unfold width PV_RDB2D_SparseShape.prefixLen;omega
 have len:(point.drop (width point)).length=trailing point := by
  rw [List.length_drop]
  change width point+trailing point=point.length at split
  omega
 simpa only [suffix,len] using h

#print axioms bits_bound
#print axioms split
#print axioms suffix_bound
end R1Z.PV_OWNI_Scanner

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNJ_Rows
open PV_OWNI_RawOps PV_OWNI_Scanner

theorem equal_iff (a b : Q) : equal a b = true ↔ a = b := by
  simp only [equal, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h0,h1⟩,h2⟩,h3⟩
    cases a with | mk ac0 ac1 =>
     cases b with | mk bc0 bc1 =>
      cases ac0; cases ac1; cases bc0; cases bc1
      dsimp only at h0 h1 h2 h3
      cases Aeneas.Std.UScalar.eq_of_val_eq h0
      cases Aeneas.Std.UScalar.eq_of_val_eq h1
      cases Aeneas.Std.UScalar.eq_of_val_eq h2
      cases Aeneas.Std.UScalar.eq_of_val_eq h3
      rfl
  · intro h; subst b; simp

theorem boolean_iff (a : Q) : boolean a = true ↔ a = zero ∨ a = one := by
  simp only [boolean, Bool.or_eq_true, equal_iff]

/-- Native row shift/OR is uniquely decoded by quotient and remainder. -/
theorem row_decode (pref trailing suffix : Nat) (hs : suffix < 2^trailing) :
 let row := PV_RDB2D_SparseAddress.row pref trailing suffix
 row / 2^trailing = pref ∧ row % 2^trailing = suffix := by
  constructor
  · exact PV_RDB2D_SparseAddress.quotient trailing suffix pref hs
  · exact Nat.mul_add_mod_of_lt hs

theorem takeWhile_take_length {A : Type} (p : A → Bool) (xs : List A) :
 xs.take (xs.takeWhile p).length = xs.takeWhile p := by
 induction xs with
 | nil => rfl
 | cons x xs ih =>
  cases h:p x <;> simp only [List.takeWhile_cons,h,Bool.false_eq_true,
   if_false,if_true,List.length_nil,List.take_zero,List.length_cons,List.take_succ_cons,ih]

theorem takeWhile_mem {A : Type} (p : A → Bool) (xs : List A) :
 ∀ x ∈ xs.takeWhile p, p x = true := by
 induction xs with
 | nil => simp
 | cons x xs ih =>
  cases h:p x <;> simp only [List.takeWhile_cons,h,Bool.false_eq_true,if_false,if_true]
  · simp
  · intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h
    · exact ih y hy

/-- The scanner drops exactly the Boolean suffix, in its original order. -/
theorem suffix_boolean (point : List Q) :
 ∀ x ∈ point.drop (width point), boolean x = true := by
 have hb := PV_RDB2D_SparseShape.trailing_bound boolean point
 have hr : (point.drop (width point)).reverse = point.reverse.takeWhile boolean := by
  rw [List.reverse_drop]
  unfold width PV_RDB2D_SparseShape.prefixLen
  have hn : point.length - (point.length - PV_RDB2D_SparseShape.trailing boolean point) =
    PV_RDB2D_SparseShape.trailing boolean point := by omega
  rw [hn]
  exact takeWhile_take_length boolean point.reverse
 intro x hx
 have hm : x ∈ point.reverse.takeWhile boolean := by
  rw [← hr]; exact List.mem_reverse.mpr hx
 exact takeWhile_mem boolean point.reverse x hm

#print axioms equal_iff
#print axioms boolean_iff
#print axioms row_decode
#print axioms takeWhile_take_length
#print axioms takeWhile_mem
#print axioms suffix_boolean
end R1Z.PV_OWNJ_Rows

end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNI_DensePrune
open scoped BigOperators
variable {K : Type} [Field K]
/-- Symbolic prefix/suffix equality weight. No concrete Boolean cube reduces. -/
def weight {I : Type} [Fintype I] (p : I → K) (b : I → Bool) : K :=
 ∏ i,if b i then p i else 1-p i

theorem boolean_weight {I : Type} [Fintype I] [DecidableEq I] (s b : I → Bool) :
 weight (fun i=>if s i then (1:K) else 0) b=if b=s then 1 else 0 := by
 classical
 by_cases h:b=s
 · subst b
   rw [if_pos rfl]
   unfold weight
   apply Finset.prod_eq_one
   intro i hi
   cases hsi:s i <;> simp [hsi]
 · rw [if_neg h]
   obtain ⟨i,hi⟩:∃ i,b i≠s i:=Function.ne_iff.mp h
   apply Finset.prod_eq_zero (Finset.mem_univ i)
   cases hb:b i <;> cases hs:s i <;> simp_all

theorem dense_sparse {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
 (p : I → K) (suffix : J → Bool) (column : (I → Bool) → (J → Bool) → K) :
 (∑ a:I → Bool,∑ b:J → Bool,
  weight p a*weight (fun j=>if suffix j then (1:K) else 0) b*column a b)=
 ∑ a:I → Bool,weight p a*column a suffix := by
 classical
 apply Finset.sum_congr rfl
 intro a ha
 simp only [boolean_weight]
 simp
#print axioms boolean_weight
#print axioms dense_sparse
end R1Z.PV_OWNI_DensePrune

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNL_RowEnumeration
open scoped BigOperators
open PV_OWNI_DensePrune

def tail (n : Nat) (a : Fin (2^n)) (i : Fin n) : Bool := a.val.testBit (n-1-i.val)

theorem tail_injective (n : Nat) : Function.Injective (tail n) := by
 intro a b h
 apply Fin.ext
 apply Nat.eq_of_testBit_eq
 intro i
 by_cases hi : i<n
 · have hv := congrFun h (⟨n-1-i,by omega⟩ : Fin n)
   have he : n-1-(n-1-i)=i := by omega
   simpa only [tail,he] using hv
 · have hp : 2^n≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
   rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le a.isLt hp),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le b.isLt hp)]

def join (w t : Nat) (z : Fin (2^w) × Fin (2^t)) : Fin (2^(w+t)) :=
 ⟨PV_RDB2D_SparseAddress.row z.1.val t z.2.val,by
  unfold PV_RDB2D_SparseAddress.row
  rw [Nat.pow_add]
  calc
   z.1.val*2^t+z.2.val < (z.1.val+1)*2^t := by
    have := z.2.isLt
    rw [Nat.add_mul,Nat.one_mul]; omega
   _ ≤ 2^w*2^t := Nat.mul_le_mul_right _ z.1.isLt⟩

theorem join_injective (w t : Nat) : Function.Injective (join w t) := by
 intro a b h
 have ha := PV_OWNJ_Rows.row_decode a.1.val t a.2.val a.2.isLt
 have hb := PV_OWNJ_Rows.row_decode b.1.val t b.2.val b.2.isLt
 have hq := congrArg (fun r : Fin (2^(w+t)) => r.val / 2^t) h
 have hr := congrArg (fun r : Fin (2^(w+t)) => r.val % 2^t) h
 dsimp only [join] at hq hr
 rw [ha.1,hb.1] at hq
 rw [ha.2,hb.2] at hr
 exact Prod.ext (Fin.ext hq) (Fin.ext hr)

theorem join_bijective (w t : Nat) : Function.Bijective (join w t) := by
 refine ⟨join_injective w t,?_⟩
 by_contra hn
 have hc := Fintype.card_lt_of_injective_not_surjective (join w t) (join_injective w t) hn
 simp only [Fintype.card_prod,Fintype.card_fin,Nat.pow_add] at hc
 exact (Nat.lt_irrefl _ hc)

def rowEquiv (w t : Nat) : (Fin (2^w) × Fin (2^t)) ≃ Fin (2^(w+t)) :=
 Equiv.ofBijective (join w t) (join_bijective w t)

theorem sum_join {K : Type} [AddCommMonoid K] (w t : Nat)
 (f : Fin (2^(w+t)) → K) :
 (∑ r, f r) = ∑ a : Fin (2^w), ∑ b : Fin (2^t), f (join w t (a,b)) := by
 have h := (Equiv.sum_comp (rowEquiv w t) f).symm
 change (∑ r, f r) = ∑ z : Fin (2^w) × Fin (2^t), f (join w t z) at h
 simpa only [Fintype.sum_prod_type] using h

/-- Dense evaluation in split coordinates, using every row of the integer
cube. The scanner's List-to-product and suffix-code identities are separate. -/
def denseSplit {K : Type} [Field K] (w t : Nat) (p : Fin w → K)
 (suffix : Fin (2^t)) (column : Fin (2^(w+t)) → K) : K :=
 ∑ r, let z := (rowEquiv w t).symm r
  weight p (tail w z.1) *
   weight (fun j => if tail t suffix j then (1:K) else 0) (tail t z.2) * column r

theorem dense_sparse {K : Type} [Field K] (w t : Nat) (p : Fin w → K)
 (suffix : Fin (2^t)) (column : Fin (2^(w+t)) → K) :
 denseSplit w t p suffix column =
 ∑ a : Fin (2^w), weight p (tail w a) * column (join w t (a,suffix)) := by
 classical
 have hi (z : Fin (2^w) × Fin (2^t)) : (rowEquiv w t).symm (join w t z) = z :=
  (rowEquiv w t).symm_apply_apply z
 have hb (b : Fin (2^t)) :
  weight (fun j => if tail t suffix j then (1:K) else 0) (tail t b) =
  if b=suffix then 1 else 0 := by
  rw [boolean_weight]
  by_cases h : b=suffix
  · subst b; simp only [if_pos rfl]
  · rw [if_neg (fun he => h (tail_injective t he)),if_neg h]
 unfold denseSplit
 rw [sum_join]
 simp only [hi]
 apply Finset.sum_congr rfl
 intro a ha
 simp [hb]
#print axioms tail_injective
#print axioms join_injective
#print axioms join_bijective
#print axioms sum_join
#print axioms dense_sparse
end R1Z.PV_OWNL_RowEnumeration

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNM_DenseRows
open scoped BigOperators
open PV_OWNI_DensePrune PV_OWNL_RowEnumeration
variable {K : Type} [Field K]

def fullDense (n : Nat) (p : Fin n → K) (column : Fin (2^n) → K) : K :=
 ∑ r, weight p (tail n r) * column r

theorem high_bit (w t : Nat) (a : Fin (2^w)) (b : Fin (2^t)) (i : Fin w) :
 tail (w+t) (join w t (a,b)) (Fin.castAdd t i) = tail w a i := by
 have h := (PV_OWNJ_Rows.row_decode a.val t b.val b.isLt).1
 have hh := congrArg (fun n : Nat => n.testBit (w-1-i.val)) h
 rw [Nat.testBit_div_two_pow] at hh
 have index : w+t-1-(Fin.castAdd t i).val = w-1-i.val+t := by
  simp only [Fin.coe_castAdd]; omega
 simpa only [tail,join,index] using hh

theorem low_bit (w t : Nat) (a : Fin (2^w)) (b : Fin (2^t)) (i : Fin t) :
 tail (w+t) (join w t (a,b)) (Fin.natAdd w i) = tail t b i := by
 have h := (PV_OWNJ_Rows.row_decode a.val t b.val b.isLt).2
 have hh := congrArg (fun n : Nat => n.testBit (t-1-i.val)) h
 have hi : t-1-i.val<t := by omega
 rw [Nat.testBit_mod_two_pow] at hh
 simp only [show decide (t-1-i.val<t)=true from by simp [hi],Bool.true_and] at hh
 have index : w+t-1-(Fin.natAdd w i).val = t-1-i.val := by
  simp only [Fin.coe_natAdd]; omega
 simpa only [tail,join,index] using hh

/-- Full-coordinate dense weights agree with the integer joined-row weights.
Neither side defines the other through rowEquiv.symm. -/
theorem joined_weight (w t : Nat) (p : Fin (w+t) → K)
 (a : Fin (2^w)) (b : Fin (2^t)) :
 weight p (tail (w+t) (join w t (a,b))) =
 weight (fun i => p (Fin.castAdd t i)) (tail w a) *
 weight (fun i => p (Fin.natAdd w i)) (tail t b) := by
 unfold weight
 rw [Fin.prod_univ_add]
 simp only [high_bit,low_bit]

/-- Ordinary full-row dense evaluation prunes to the scanner suffix, provided
its decoded suffix coordinates are the published Boolean bits. -/
theorem full_dense_sparse (w t : Nat) (p : Fin (w+t) → K)
 (suffix : Fin (2^t)) (column : Fin (2^(w+t)) → K)
 (hs : ∀ i : Fin t, p (Fin.natAdd w i) = if tail t suffix i then 1 else 0) :
 fullDense (w+t) p column =
 ∑ a : Fin (2^w), weight (fun i => p (Fin.castAdd t i)) (tail w a) *
  column (join w t (a,suffix)) := by
 classical
 unfold fullDense
 rw [sum_join]
 apply Finset.sum_congr rfl
 intro a ha
 simp only [joined_weight]
 have hp : (fun i : Fin t => p (Fin.natAdd w i)) =
  (fun i => if tail t suffix i then (1:K) else 0) := funext hs
 rw [hp]
 have hb (b : Fin (2^t)) :
  weight (fun i => if tail t suffix i then (1:K) else 0) (tail t b) =
  if b=suffix then 1 else 0 := by
  rw [boolean_weight]
  by_cases h : b=suffix
  · subst b; simp
  · rw [if_neg (fun he => h (tail_injective t he)),if_neg h]
 simp [hb]

#print axioms high_bit
#print axioms low_bit
#print axioms joined_weight
#print axioms full_dense_sparse
end R1Z.PV_OWNM_DenseRows

end
end

section
set_option autoImplicit false
namespace R1Z.PV_OWNK_ReduceNat
def P : Nat := 2147483647
def fold31 (x : Nat) : Nat := x % 2147483648 + x / 2147483648
def subtractP (x : Nat) : Nat := if x ≥ P then x-P else x
def reduce64 (x : Nat) : Nat := subtractP (fold31 (fold31 x))
theorem first_bound (x : Nat) (hx : x < 18446744073709551616) :
 fold31 x ≤ 10737418238 := by
 unfold fold31
 have := Nat.mod_lt x (by omega : 0 < 2147483648)
 have : x / 2147483648 ≤ 8589934591 := by omega
 omega
theorem second_bound (x : Nat) (hx : x ≤ 10737418238) :
 fold31 x ≤ 2147483651 := by
 unfold fold31
 have := Nat.mod_lt x (by omega : 0 < 2147483648)
 have : x / 2147483648 ≤ 4 := by omega
 omega
theorem canonical (x : Nat) (hx : x < 18446744073709551616) : reduce64 x < P := by
 have := second_bound _ (first_bound x hx)
 unfold reduce64 subtractP P
 split <;> omega
theorem fold_mod (x : Nat) : fold31 x % P = x % P := by
 have h := Nat.mod_add_div x 2147483648
 have he : fold31 x + P * (x / 2147483648) = x := by unfold fold31 P; omega
 calc
  fold31 x % P = (fold31 x + P * (x / 2147483648)) % P := by
   rw [Nat.add_mod,Nat.mul_mod]; simp
  _ = x % P := congrArg (fun y => y % P) he
theorem subtract_mod (x : Nat) : subtractP x % P = x % P := by
 unfold subtractP
 split
 · rename_i h
   calc
    (x-P)%P = ((x-P)+P)%P := (Nat.add_mod_right (x-P) P).symm
    _ = x%P := congrArg (fun y => y%P) (Nat.sub_add_cancel h)
 · rfl
theorem exact_mod (x : Nat) (hx : x < 18446744073709551616) : reduce64 x = x % P := by
 have h : reduce64 x % P = x % P := by
  unfold reduce64
  rw [subtract_mod,fold_mod,fold_mod]
 rw [Nat.mod_eq_of_lt (canonical x hx)] at h
 exact h
#print axioms first_bound
#print axioms second_bound
#print axioms canonical
#print axioms fold_mod
#print axioms subtract_mod
#print axioms exact_mod
end R1Z.PV_OWNK_ReduceNat

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNK_ReduceBits
open PV_OWNK_ReduceNat
def fold64 (x : BitVec 64) : BitVec 64 := (x &&& 2147483647#64) + (x >>> 31)
def word (x : BitVec 64) : BitVec 32 := (fold64 (fold64 x)).setWidth 32
def reduced (x : BitVec 64) : BitVec 32 :=
 word x - (2147483647#32 &&& (0#32 - (if (2147483647#32).ule (word x) then 1#32 else 0#32)))
theorem fold_val (x : BitVec 64) : (fold64 x).toNat = fold31 x.toNat := by
 have hb := first_bound x.toNat x.isLt
 have he : (fold64 x).toNat = fold31 x.toNat % 18446744073709551616 := by
  simp only [fold64,BitVec.toNat_add,BitVec.toNat_and,BitVec.toNat_ushiftRight,
   Nat.shiftRight_eq_div_pow]
  change ((x.toNat &&& (2^31-1)) + x.toNat / 2147483648) % 18446744073709551616 = _
  rw [Nat.and_two_pow_sub_one_eq_mod]
  rfl
 rw [he,Nat.mod_eq_of_lt (by omega)]
theorem word_val (x : BitVec 64) : (word x).toNat = fold31 (fold31 x.toNat) := by
 have hb := second_bound _ (first_bound x.toNat x.isLt)
 rw [word,BitVec.toNat_setWidth,fold_val,fold_val]
 exact Nat.mod_eq_of_lt (by omega)
theorem reduced_val (x : BitVec 64) : (reduced x).toNat = reduce64 x.toNat := by
 have hw := word_val x
 have hb := second_bound _ (first_bound x.toNat x.isLt)
 by_cases h : 2147483647 ≤ (word x).toNat
 · simp only [reduced,BitVec.ule,show (2147483647#32).toNat = 2147483647 from rfl,
    h,decide_true,if_pos]
   change (word x - 2147483647#32).toNat = _
   rw [BitVec.toNat_sub_of_le (show 2147483647#32 ≤ word x from h)]
   change (word x).toNat - 2147483647 = _
   rw [hw]
   unfold reduce64 subtractP P
   rw [if_pos (by omega)]
 · simp only [reduced,BitVec.ule,show (2147483647#32).toNat = 2147483647 from rfl,
    h,decide_false,if_neg]
   change (word x - 0#32).toNat = _
   rw [BitVec.sub_zero,hw]
   unfold reduce64 subtractP P
   rw [if_neg (by omega)]
theorem decode (x : BitVec 64) : (reduced x).toNat = x.toNat % 2147483647 := by
 rw [reduced_val,exact_mod x.toNat x.isLt]
 rfl
#print axioms fold_val
#print axioms word_val
#print axioms reduced_val
#print axioms decode
end R1Z.PV_OWNK_ReduceBits

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNK_CTDecode
open Aeneas Aeneas.Std
abbrev subtract := PV_B2_FieldValue.aspis_core.field.ct.subtract_p
abbrev add := PV_B2_FieldValue.aspis_core.field.ct.add
abbrev sub := PV_B2_FieldValue.aspis_core.field.ct.sub
abbrev P := PV_B2_FieldValue.aspis_core.field.P

theorem sub_zero (x : U32) : U32.wrapping_sub x 0#u32 = x := by
 apply UScalar.eq_of_val_eq
 rw [U32.wrapping_sub_val_eq]
 simp only [show (0#u32).val=0 from rfl,Nat.sub_zero,Nat.add_mod_right]
 rw [UScalar.size]
 exact Nat.mod_eq_of_lt x.hBounds

theorem subtract_shape (x : U32) : subtract x =
 if x ≥ P then U32.wrapping_sub x P else x := by
 unfold subtract PV_B2_FieldValue.aspis_core.field.ct.subtract_p
 by_cases h : x ≥ P
 · simp only [h,decide_true,if_pos]
   rfl
 · simp only [h,decide_false,if_neg]
   change U32.wrapping_sub x 0#u32 = x
   exact sub_zero x

theorem subtract_decode (x : U32) (hx : x.val < 4294967294) :
 (subtract x).val = x.val % 2147483647 := by
 rw [subtract_shape]
 by_cases h : x ≥ P
 · rw [if_pos h,U32.wrapping_sub_val_eq,UScalar.size]
   change (x.val + (4294967296 - 2147483647)) % 4294967296 = x.val % 2147483647
   change 2147483647 ≤ x.val at h
   omega
 · rw [if_neg h]
   change ¬ 2147483647 ≤ x.val at h
   exact (Nat.mod_eq_of_lt (by omega)).symm

theorem add_decode (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (add a b).val = (a.val+b.val) % 2147483647 := by
 have hv : (core.num.U32.wrapping_add a b).val = a.val+b.val := by
  rw [core.num.U32.wrapping_add_val_eq,UScalar.size]
  change (a.val+b.val)%4294967296 = a.val+b.val
  omega
 unfold add PV_B2_FieldValue.aspis_core.field.ct.add
 rw [subtract_decode _ (by rw [hv];omega),hv]

theorem sub_decode (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (sub a b).val = (a.val+2147483647-b.val) % 2147483647 := by
 have hv : (core.num.U32.wrapping_sub (core.num.U32.wrapping_add a P) b).val = a.val+2147483647-b.val := by
  rw [core.num.U32.wrapping_sub_val_eq,core.num.U32.wrapping_add_val_eq,UScalar.size]
  change ((a.val+2147483647)%4294967296+(4294967296-b.val))%4294967296 = _
  omega
 unfold sub PV_B2_FieldValue.aspis_core.field.ct.sub
 rw [subtract_decode _ (by rw [hv];omega),hv]

/-- The CT reducer used by the actual raw multiplication, not the ordinary
arithmetic extraction's reducer. -/
theorem reduce_shape (x : U64) :
 (PV_B2_FieldValue.aspis_core.field.ct.reduce64 x).val =
 (PV_OWNK_ReduceBits.reduced x.bv).toNat := by
 unfold PV_B2_FieldValue.aspis_core.field.ct.reduce64
  PV_B2_FieldValue.aspis_core.field.ct.subtract_p
  PV_B2_FieldValue.aspis_core.field.P
 simp only [UScalar.lt_equiv,UScalar.le_equiv,UScalar.val,UScalar.cast,
  UScalar.cast_fromBool,UScalar.wrapping_shr,core.num.U32.wrapping_sub,
  U64.wrapping_add,U64.wrapping_shr,UScalar.wrapping_add,UScalar.wrapping_sub,
  UScalar.bv_and,UScalarTy.numBits,BitVec.zeroExtend_eq_setWidth,decide_eq_true_eq,
  U32.ofNat_bv]
 simp only [show BitVec.setWidth 64 2147483647#32 = 2147483647#64 from by decide,
  show (31#32).toNat % 64 = 31 from rfl,
  show (2147483647#32).toNat = 2147483647 from rfl]
 norm_num only [PV_OWNK_ReduceBits.reduced,PV_OWNK_ReduceBits.word,
  PV_OWNK_ReduceBits.fold64,BitVec.ule,decide_eq_true_eq,apply_ite,HShiftRight.hShiftRight]
 simp only [show (2147483647#32).toNat = 2147483647 from rfl]
 split <;> rename_i h <;> simp only [h,if_pos,if_neg]

theorem reduce_decode (x : U64) :
 (PV_B2_FieldValue.aspis_core.field.ct.reduce64 x).val = x.val % 2147483647 := by
 rw [reduce_shape,PV_OWNK_ReduceBits.decode]
 rfl

theorem reduce_canon (x : U64) :
 (PV_B2_FieldValue.aspis_core.field.ct.reduce64 x).val < 2147483647 := by
 rw [reduce_decode]
 exact Nat.mod_lt _ (by omega)

theorem add_canon (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (add a b).val < 2147483647 := by
 rw [add_decode a b ha hb]
 exact Nat.mod_lt _ (by omega)

theorem sub_canon (a b : U32) (ha : a.val < 2147483647) (hb : b.val < 2147483647) :
 (sub a b).val < 2147483647 := by
 rw [sub_decode a b ha hb]
 exact Nat.mod_lt _ (by omega)

#print axioms reduce_shape
#print axioms reduce_decode
#print axioms reduce_canon
#print axioms add_canon
#print axioms sub_canon
#print axioms sub_zero
#print axioms subtract_shape
#print axioms subtract_decode
#print axioms add_decode
#print axioms sub_decode
end R1Z.PV_OWNK_CTDecode

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNK_ScalarOps
open Aeneas Aeneas.Std
abbrev M := PV_B2_FieldValue.aspis_core.field.M31
abbrev Canon (x : U32) : Prop := x.val < 2147483647

theorem mul_canon (a b : U32) : Canon (PV_B2_FieldValue.aspis_core.field.M31.mul a b) :=
 PV_OWNK_CTDecode.reduce_canon _

theorem mul_decode (a b : U32) :
 (PV_B2_FieldValue.aspis_core.field.M31.mul a b).val = (a.val*b.val) % 2147483647 := by
 have ha : a.val < 4294967296 := a.hBounds
 have hb : b.val < 4294967296 := b.hBounds
 have hac : (UScalar.cast .U64 a).val = a.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by change a.val < 18446744073709551616; omega)
 have hbc : (UScalar.cast .U64 b).val = b.val := by
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by change b.val < 18446744073709551616; omega)
 have hp : a.val*b.val < 18446744073709551616 := by
  change a.val < 4294967296 at ha
  change b.val < 4294967296 at hb
  nlinarith
 unfold PV_B2_FieldValue.aspis_core.field.M31.mul
  PV_B2_FieldValue.aspis_core.field.reduce_u64
 rw [PV_OWNK_CTDecode.reduce_decode,U64.wrapping_mul_val_eq,hac,hbc,UScalar.size]
 change (a.val*b.val)%18446744073709551616%2147483647 = (a.val*b.val)%2147483647
 rw [Nat.mod_eq_of_lt hp]

theorem reduce_canon (a : U64) : Canon (PV_B2_FieldValue.aspis_core.field.M31.reduce_u64 a) :=
 PV_OWNK_CTDecode.reduce_canon _

theorem add_canon (a b : U32) (ha : Canon a) (hb : Canon b) : Canon (PV_B2_FieldValue.aspis_core.field.M31.add a b) :=
 PV_OWNK_CTDecode.add_canon a b ha hb

theorem sub_canon (a b : U32) (ha : Canon a) (hb : Canon b) : Canon (PV_B2_FieldValue.aspis_core.field.M31.sub a b) :=
 PV_OWNK_CTDecode.sub_canon a b ha hb

theorem double_canon (a : U32) (ha : Canon a) : Canon (PV_B2_FieldValue.aspis_core.field.M31.double a) := add_canon a a ha ha

#print axioms mul_canon
#print axioms mul_decode
#print axioms reduce_canon
#print axioms add_canon
#print axioms sub_canon
#print axioms double_canon
end R1Z.PV_OWNK_ScalarOps

end

section
set_option autoImplicit false
namespace R1Z.PV_OWNK_TowerCanon
open Aeneas Aeneas.Std
abbrev Q := ProverRwFull.aspis_core.field.QM31
abbrev valueAdd := PV_B2_FieldValue.aspis_core.field.QM31.add
abbrev valueMul := PV_B2_FieldValue.aspis_core.field.QM31.mul
abbrev valueSub := PV_B2_FieldValue.aspis_core.field.QM31.sub
abbrev zero := PV_B2_FieldValue.aspis_core.field.QM31.ZERO
abbrev one := PV_B2_FieldValue.aspis_core.field.QM31.ONE
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev CM := PV_B2_FieldValue.aspis_core.field.CM31
abbrev QM := PV_B2_FieldValue.aspis_core.field.QM31
def CC (x : C) : Prop := PV_OWNK_ScalarOps.Canon x.a ∧ PV_OWNK_ScalarOps.Canon x.b
def Canon (x : Q) : Prop := CC x.c0 ∧ CC x.c1

theorem cm_add (x y : C) (hx : CC x) (hy : CC y) : CC (PV_B2_FieldValue.aspis_core.field.CM31.add x y) :=
 ⟨PV_OWNK_ScalarOps.add_canon _ _ hx.1 hy.1,PV_OWNK_ScalarOps.add_canon _ _ hx.2 hy.2⟩
theorem cm_sub (x y : C) (hx : CC x) (hy : CC y) : CC (PV_B2_FieldValue.aspis_core.field.CM31.sub x y) :=
 ⟨PV_OWNK_ScalarOps.sub_canon _ _ hx.1 hy.1,PV_OWNK_ScalarOps.sub_canon _ _ hx.2 hy.2⟩
/-- The three partial products are reduced even for arbitrary raw inputs. -/
theorem cm_mul (x y : C) : CC (PV_B2_FieldValue.aspis_core.field.CM31.mul x y) := by
 change PV_OWNK_ScalarOps.Canon _ ∧ PV_OWNK_ScalarOps.Canon _
 constructor
 · exact PV_OWNK_ScalarOps.sub_canon _ _
    (PV_OWNK_ScalarOps.mul_canon _ _) (PV_OWNK_ScalarOps.mul_canon _ _)
 · exact PV_OWNK_ScalarOps.sub_canon _ _
    (PV_OWNK_ScalarOps.sub_canon _ _ (PV_OWNK_ScalarOps.reduce_canon _)
     (PV_OWNK_ScalarOps.mul_canon _ _)) (PV_OWNK_ScalarOps.mul_canon _ _)

theorem mul_by_r (x : C) (hx : CC x) :
 CC (PV_B2_FieldValue.aspis_core.field.mul_by_r x) :=
 ⟨PV_OWNK_ScalarOps.sub_canon _ _ (PV_OWNK_ScalarOps.double_canon _ hx.1) hx.2,
  PV_OWNK_ScalarOps.add_canon _ _ hx.1 (PV_OWNK_ScalarOps.double_canon _ hx.2)⟩
theorem zero_canon : Canon zero := by
 constructor <;> constructor <;> change 0 < 2147483647 <;> omega
theorem one_canon : Canon one := by
 constructor
 · exact ⟨by change 1 < 2147483647; omega,by change 0 < 2147483647; omega⟩
 · constructor <;> change 0 < 2147483647 <;> omega
theorem qm_add (x y : Q) (hx : Canon x) (hy : Canon y) : Canon (valueAdd x y) :=
 ⟨cm_add _ _ hx.1 hy.1,cm_add _ _ hx.2 hy.2⟩
theorem qm_sub (x y : Q) (hx : Canon x) (hy : Canon y) : Canon (valueSub x y) :=
 ⟨cm_sub _ _ hx.1 hy.1,cm_sub _ _ hx.2 hy.2⟩
theorem qm_mul (x y : Q) : Canon (valueMul x y) :=
 ⟨cm_add _ _ (cm_mul _ _) (mul_by_r _ (cm_mul _ _)),
  cm_sub _ _ (cm_sub _ _ (cm_mul _ _) (cm_mul _ _)) (cm_mul _ _)⟩
#print axioms cm_add
#print axioms cm_sub
#print axioms cm_mul
#print axioms mul_by_r
#print axioms zero_canon
#print axioms one_canon
#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
end R1Z.PV_OWNK_TowerCanon

end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNK_FieldScalar
open Aeneas Aeneas.Std
open PV_OWNK_ScalarOps
abbrev F := AspisV8R15.ExactTowerBase.M31Exact
def decode (x : U32) : F := x.val

theorem add (a b : U32) (ha : Canon a) (hb : Canon b) :
 decode (PV_B2_FieldValue.aspis_core.field.M31.add a b) = decode a + decode b := by
 change ((PV_OWNK_CTDecode.add a b).val : F) = _
 rw [PV_OWNK_CTDecode.add_decode a b ha hb,ZMod.natCast_mod,Nat.cast_add]
 rfl
theorem sub (a b : U32) (ha : Canon a) (hb : Canon b) :
 decode (PV_B2_FieldValue.aspis_core.field.M31.sub a b) = decode a - decode b := by
 change ((PV_OWNK_CTDecode.sub a b).val : F) = _
 rw [PV_OWNK_CTDecode.sub_decode a b ha hb,ZMod.natCast_mod,
  Nat.cast_sub (show b.val ≤ a.val+2147483647 by unfold Canon at hb; omega),Nat.cast_add]
 rw [show ((2147483647 : Nat) : F)=0 from ZMod.natCast_self 2147483647,add_zero]
 rfl
theorem mul (a b : U32) : decode (PV_B2_FieldValue.aspis_core.field.M31.mul a b) = decode a * decode b := by
 unfold decode
 rw [mul_decode,ZMod.natCast_mod,Nat.cast_mul]
theorem reduce (a : U64) : decode (PV_B2_FieldValue.aspis_core.field.M31.reduce_u64 a) = (a.val : F) := by
 unfold decode PV_B2_FieldValue.aspis_core.field.M31.reduce_u64
  PV_B2_FieldValue.aspis_core.field.reduce_u64
 rw [PV_OWNK_CTDecode.reduce_decode,ZMod.natCast_mod]
theorem double (a : U32) (ha : Canon a) : decode (PV_B2_FieldValue.aspis_core.field.M31.double a) = decode a + decode a :=
 add a a ha ha
#print axioms add
#print axioms sub
#print axioms mul
#print axioms reduce
#print axioms double
end R1Z.PV_OWNK_FieldScalar

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNK_CMDecode
open Aeneas Aeneas.Std
open PV_OWNK_TowerCanon
abbrev F := PV_OWNK_FieldScalar.F
abbrev E := AspisV8R15.ExactTowerBase.CM31Exact
abbrev M := PV_OWNK_ScalarOps.M
abbrev ds := PV_OWNK_FieldScalar.decode
def decode (x : C) : E := ⟨ds x.a,ds x.b⟩

theorem add (x y : C) (hx : CC x) (hy : CC y) :
 decode (PV_B2_FieldValue.aspis_core.field.CM31.add x y) = decode x + decode y := by
 apply QuadraticAlgebra.ext
 · exact PV_OWNK_FieldScalar.add _ _ hx.1 hy.1
 · exact PV_OWNK_FieldScalar.add _ _ hx.2 hy.2

theorem sub (x y : C) (hx : CC x) (hy : CC y) :
 decode (PV_B2_FieldValue.aspis_core.field.CM31.sub x y) = decode x - decode y := by
 apply QuadraticAlgebra.ext
 · exact PV_OWNK_FieldScalar.sub _ _ hx.1 hy.1
 · exact PV_OWNK_FieldScalar.sub _ _ hx.2 hy.2

def cross (x y : C) : U64 :=
 U64.wrapping_mul
  (U64.wrapping_add (core.convert.num.FromU64U32.from x.a) (core.convert.num.FromU64U32.from x.b))
  (U64.wrapping_add (core.convert.num.FromU64U32.from y.a) (core.convert.num.FromU64U32.from y.b))

theorem cross_val (x y : C) (hx : CC x) (hy : CC y) :
 (cross x y).val = (x.a.val+x.b.val)*(y.a.val+y.b.val) := by
 have cast_val (a : U32) : (core.convert.num.FromU64U32.from a).val = a.val := by
  change (UScalar.cast .U64 a).val = a.val
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by have h : a.val < 4294967296 := a.hBounds; change a.val < 18446744073709551616; omega)
 have ha : x.a.val+x.b.val < 4294967296 := by obtain ⟨ha,hb⟩:=hx; unfold PV_OWNK_ScalarOps.Canon at ha hb; omega
 have hb : y.a.val+y.b.val < 4294967296 := by obtain ⟨ha,hb⟩:=hy; unfold PV_OWNK_ScalarOps.Canon at ha hb; omega
 unfold cross
 rw [U64.wrapping_mul_val_eq,U64.wrapping_add_val_eq,U64.wrapping_add_val_eq,
  cast_val,cast_val,cast_val,cast_val,UScalar.size]
 change ((x.a.val+x.b.val)%18446744073709551616 *
  ((y.a.val+y.b.val)%18446744073709551616))%18446744073709551616 = _
 rw [Nat.mod_eq_of_lt (show x.a.val+x.b.val < 18446744073709551616 by omega),
  Nat.mod_eq_of_lt (show y.a.val+y.b.val < 18446744073709551616 by omega)]
 exact Nat.mod_eq_of_lt (by nlinarith)

theorem mul (x y : C) (hx : CC x) (hy : CC y) :
 decode (PV_B2_FieldValue.aspis_core.field.CM31.mul x y) = decode x * decode y := by
 have h0 := PV_OWNK_ScalarOps.mul_canon x.a y.a
 have h1 := PV_OWNK_ScalarOps.mul_canon x.b y.b
 have h2 := PV_OWNK_ScalarOps.reduce_canon (cross x y)
 apply QuadraticAlgebra.ext
 · change ds (PV_B2_FieldValue.aspis_core.field.M31.sub (PV_B2_FieldValue.aspis_core.field.M31.mul x.a y.a) (PV_B2_FieldValue.aspis_core.field.M31.mul x.b y.b)) = _
   simp only [ds]
   rw [PV_OWNK_FieldScalar.sub _ _ h0 h1,PV_OWNK_FieldScalar.mul,PV_OWNK_FieldScalar.mul]
   simp only [QuadraticAlgebra.re_mul,decode]
   ring
 · change ds (PV_B2_FieldValue.aspis_core.field.M31.sub (PV_B2_FieldValue.aspis_core.field.M31.sub (PV_B2_FieldValue.aspis_core.field.M31.reduce_u64 (cross x y)) (PV_B2_FieldValue.aspis_core.field.M31.mul x.a y.a)) (PV_B2_FieldValue.aspis_core.field.M31.mul x.b y.b)) = _
   simp only [ds]
   rw [PV_OWNK_FieldScalar.sub _ _ (PV_OWNK_ScalarOps.sub_canon _ _ h2 h0) h1,
    PV_OWNK_FieldScalar.sub _ _ h2 h0,PV_OWNK_FieldScalar.reduce,
    cross_val x y hx hy, Nat.cast_mul,Nat.cast_add,Nat.cast_add,
    PV_OWNK_FieldScalar.mul,PV_OWNK_FieldScalar.mul]
   simp only [QuadraticAlgebra.im_mul,decode,PV_OWNK_FieldScalar.decode]
   ring

theorem mul_by_r (x : C) (hx : CC x) :
 decode (PV_B2_FieldValue.aspis_core.field.mul_by_r x) =
 AspisV8R15.ExactTowerBase.qm31R * decode x := by
 apply QuadraticAlgebra.ext
 · change ds (PV_B2_FieldValue.aspis_core.field.M31.sub (PV_B2_FieldValue.aspis_core.field.M31.double x.a) x.b) = _
   simp only [ds]
   rw [PV_OWNK_FieldScalar.sub _ _ (PV_OWNK_ScalarOps.double_canon _ hx.1) hx.2,
    PV_OWNK_FieldScalar.double _ hx.1]
   simp only [QuadraticAlgebra.re_mul,decode,AspisV8R15.ExactTowerBase.qm31R]
   ring
 · change ds (PV_B2_FieldValue.aspis_core.field.M31.add x.a (PV_B2_FieldValue.aspis_core.field.M31.double x.b)) = _
   simp only [ds]
   rw [PV_OWNK_FieldScalar.add _ _ hx.1 (PV_OWNK_ScalarOps.double_canon _ hx.2),
    PV_OWNK_FieldScalar.double _ hx.2]
   simp only [QuadraticAlgebra.im_mul,decode,AspisV8R15.ExactTowerBase.qm31R]
   ring

#print axioms add
#print axioms sub
#print axioms cross_val
#print axioms mul
#print axioms mul_by_r
end R1Z.PV_OWNK_CMDecode

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNK_QMDecode
open PV_OWNK_TowerCanon
abbrev K := AspisV8R15.ExactTowerBase.QM31Exact
abbrev dc := PV_OWNK_CMDecode.decode
def decode (x : Q) : K := ⟨dc x.c0,dc x.c1⟩

theorem zero : decode PV_OWNK_TowerCanon.zero = 0 := by
 apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> rfl
theorem one : decode PV_OWNK_TowerCanon.one = 1 := by
 apply QuadraticAlgebra.ext <;> apply QuadraticAlgebra.ext <;> rfl

theorem add (x y : Q) (hx : Canon x) (hy : Canon y) :
 decode (valueAdd x y) = decode x + decode y := by
 apply QuadraticAlgebra.ext
 · exact PV_OWNK_CMDecode.add _ _ hx.1 hy.1
 · exact PV_OWNK_CMDecode.add _ _ hx.2 hy.2

theorem sub (x y : Q) (hx : Canon x) (hy : Canon y) :
 decode (valueSub x y) = decode x - decode y := by
 apply QuadraticAlgebra.ext
 · exact PV_OWNK_CMDecode.sub _ _ hx.1 hy.1
 · exact PV_OWNK_CMDecode.sub _ _ hx.2 hy.2

theorem mul (x y : Q) (hx : Canon x) (hy : Canon y) :
 decode (valueMul x y) = decode x * decode y := by
 have hm0 := cm_mul x.c0 y.c0
 have hm1 := cm_mul x.c1 y.c1
 have hsx := cm_add x.c0 x.c1 hx.1 hx.2
 have hsy := cm_add y.c0 y.c1 hy.1 hy.2
 have hm2 := cm_mul (PV_B2_FieldValue.aspis_core.field.CM31.add x.c0 x.c1) (PV_B2_FieldValue.aspis_core.field.CM31.add y.c0 y.c1)
 apply QuadraticAlgebra.ext
 · change dc (PV_B2_FieldValue.aspis_core.field.CM31.add (PV_B2_FieldValue.aspis_core.field.CM31.mul x.c0 y.c0)
    (PV_B2_FieldValue.aspis_core.field.mul_by_r (PV_B2_FieldValue.aspis_core.field.CM31.mul x.c1 y.c1))) = _
   simp only [dc]
   rw [PV_OWNK_CMDecode.add _ _ hm0 (mul_by_r _ hm1),
    PV_OWNK_CMDecode.mul_by_r _ hm1,
    PV_OWNK_CMDecode.mul _ _ hx.1 hy.1,PV_OWNK_CMDecode.mul _ _ hx.2 hy.2]
   simp only [decode,dc,QuadraticAlgebra.re_mul]
   ring
 · change dc (PV_B2_FieldValue.aspis_core.field.CM31.sub (PV_B2_FieldValue.aspis_core.field.CM31.sub (PV_B2_FieldValue.aspis_core.field.CM31.mul (PV_B2_FieldValue.aspis_core.field.CM31.add x.c0 x.c1) (PV_B2_FieldValue.aspis_core.field.CM31.add y.c0 y.c1))
    (PV_B2_FieldValue.aspis_core.field.CM31.mul x.c0 y.c0)) (PV_B2_FieldValue.aspis_core.field.CM31.mul x.c1 y.c1)) = _
   simp only [dc]
   rw [PV_OWNK_CMDecode.sub _ _ (cm_sub _ _ hm2 hm0) hm1,
    PV_OWNK_CMDecode.sub _ _ hm2 hm0,
    PV_OWNK_CMDecode.mul _ _ hsx hsy,
    PV_OWNK_CMDecode.add _ _ hx.1 hx.2,PV_OWNK_CMDecode.add _ _ hy.1 hy.2,
    PV_OWNK_CMDecode.mul _ _ hx.1 hy.1,PV_OWNK_CMDecode.mul _ _ hx.2 hy.2]
   simp only [decode,QuadraticAlgebra.im_mul]
   ring
#print axioms zero
#print axioms one
#print axioms add
#print axioms sub
#print axioms mul
end R1Z.PV_OWNK_QMDecode

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNJ_DecodeFold
open PV_OWNI_RawOps
attribute [local irreducible] PV_B2_FieldValue.aspis_core.field.QM31.add
 PV_B2_FieldValue.aspis_core.field.QM31.mul PV_B2_FieldValue.aspis_core.field.QM31.sub
variable {K : Type} [Field K]

/-- Canonicality is concrete, not an assumed image of the desired result. -/
def Canon (q : Q) : Prop :=
 q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
 q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

/-- Explicit stage obligations. No theorem here supplies this instance. -/
structure Decoder (decode : Q → K) : Prop where
 zero_eq : decode zero = 0
 one_eq : decode one = 1
 zero_canon : Canon zero
 one_canon : Canon one
 add : ∀ x y, Canon x → Canon y →
  Canon (valueAdd x y) ∧ decode (valueAdd x y) = decode x + decode y
 mul : ∀ x y, Canon x → Canon y →
  Canon (valueMul x y) ∧ decode (valueMul x y) = decode x * decode y
 sub : ∀ x, Canon x →
  Canon (valueSub one x) ∧ decode (valueSub one x) = 1 - decode x

theorem fold (decode : Q → K) (D : Decoder decode) (column : List Q)
 (entries : List (Nat × Q)) (initial : Q) (hi : Canon initial)
 (hc : ∀ e ∈ entries, Canon e.2 ∧ Canon (column[e.1]?.getD zero)) :
 Canon (entries.foldl (PV_OWNI_RawFold.term column) initial) ∧
 decode (entries.foldl (PV_OWNI_RawFold.term column) initial) =
 entries.foldl (fun sum e => sum + decode e.2 * decode (column[e.1]?.getD zero))
  (decode initial) := by
 induction entries generalizing initial with
 | nil => exact ⟨hi,rfl⟩
 | cons x xs ih =>
  obtain ⟨hx,hv⟩ := hc x (by simp)
  obtain ⟨hp,hdp⟩ := D.mul _ _ hx hv
  obtain ⟨ha,hda⟩ := D.add _ _ hi hp
  have hrest := ih (PV_OWNI_RawFold.term column initial x) ha
   (fun e he => hc e (by simp only [List.mem_cons]; exact Or.inr he))
  constructor
  · exact hrest.1
  · simp only [List.foldl_cons]
    rw [hrest.2]
    change xs.foldl _ (decode (valueAdd initial (valueMul x.2 _))) = _
    rw [hda,hdp]

#print axioms fold
end R1Z.PV_OWNJ_DecodeFold

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNJ_DecodeWeight
open PV_OWNI_RawOps PV_OWNJ_DecodeFold
attribute [local irreducible] PV_B2_FieldValue.aspis_core.field.QM31.add
 PV_B2_FieldValue.aspis_core.field.QM31.mul PV_B2_FieldValue.aspis_core.field.QM31.sub
variable {K : Type} [Field K]

def step (width pref : Nat) (acc : K × Nat) (coordinate : K) : K × Nat :=
 (acc.1 * (if pref.testBit (width-1-acc.2) then coordinate else 1-coordinate),acc.2+1)

theorem weight (decode : Q → K) (D : Decoder decode) (width pref : Nat)
 (coordinates : List Q) (acc : Q × Nat) (ha : Canon acc.1)
 (hc : ∀ q ∈ coordinates, Canon q) :
 let out := coordinates.foldl (PV_OWNI_WeightTotal.step width pref) acc
 Canon out.1 ∧ (decode out.1,out.2) =
 (coordinates.map decode).foldl (step width pref) (decode acc.1,acc.2) := by
 induction coordinates generalizing acc with
 | nil => exact ⟨ha,rfl⟩
 | cons q qs ih =>
  have hq := hc q (by simp)
  have hs : Canon (if pref.testBit (width-1-acc.2) then q else valueSub one q) ∧
   decode (if pref.testBit (width-1-acc.2) then q else valueSub one q) =
    (if pref.testBit (width-1-acc.2) then decode q else 1-decode q) := by
   cases h:pref.testBit (width-1-acc.2)
   · exact D.sub q hq
   · exact ⟨hq,rfl⟩
  have hm := D.mul acc.1 _ ha hs.1
  have hr := ih (PV_OWNI_WeightTotal.step width pref acc q) hm.1
   (fun x hx => hc x (by simp only [List.mem_cons]; exact Or.inr hx))
  constructor
  · exact hr.1
  · simp only [List.foldl_cons,List.map_cons]
    rw [hr.2]
    congr 1
    change (decode (valueMul acc.1 _),acc.2+1) = _
    rw [hm.2,hs.2]
    rfl

#print axioms weight
end R1Z.PV_OWNJ_DecodeWeight

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNJ_ValueBridge
open PV_OWNI_RawOps PV_OWNJ_DecodeFold
variable {K : Type} [Field K]

theorem entries_canon (decode : Q → K) (D : Decoder decode) (point : List Q)
 (hc : ∀ q ∈ point, Canon q) (width trailing suffix : Nat) :
 ∀ e ∈ PV_OWNI_BuildTotal.entries point width trailing suffix, Canon e.2 := by
 intro e he
 obtain ⟨pref,hp,rfl⟩ := List.mem_map.mp he
 simp only [one_value]
 exact (PV_OWNJ_DecodeWeight.weight decode D width pref (point.take width) (one,0)
  D.one_canon (fun q hq => hc q (List.mem_of_mem_take hq))).1

/-- Ordered sparse field fold at exactly the scanner's width, trailing and
suffix. The concrete Decoder instance and dense row transport remain open. -/
def sparse (decode : Q → K) (point column : List Q) : K :=
 (PV_OWNI_BuildTotal.entries point (PV_OWNI_Scanner.width point)
  (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)).foldl
 (fun sum e => sum + decode e.2 * decode (column[e.1]?.getD zero)) 0

theorem value_commutes (decode : Q → K) (D : Decoder decode) (point column : List Q)
 (hp : ∀ q ∈ point, Canon q) (hc : ∀ q ∈ column, Canon q) :
 (PV_OWNI_RawConsumer.value point column (PV_OWNI_Scanner.width point)
  (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)).map decode =
 if column.length ≠ 1024 then none else some (sparse decode point column) := by
 unfold PV_OWNI_RawConsumer.value
 split
 · rfl
 · rename_i h
   have hv := PV_OWNJ_DecodeFold.fold decode D column
    (PV_OWNI_BuildTotal.entries point (PV_OWNI_Scanner.width point)
     (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)) zero D.zero_canon
    (fun e he => ⟨entries_canon decode D point hp _ _ _ e he, by
      cases hx : column[e.1]? with
      | none => exact D.zero_canon
      | some q => exact hc q (List.mem_of_getElem? hx)⟩)
   simp only [Option.map_some]
   rw [hv.2,D.zero_eq]
   rfl

#print axioms entries_canon
#print axioms value_commutes
end R1Z.PV_OWNJ_ValueBridge

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNK_ConcreteDecoder
open Aeneas Aeneas.Std Result
open PV_OWNI_RawOps
abbrev decode := PV_OWNK_QMDecode.decode
abbrev K := PV_OWNK_QMDecode.K
abbrev Canon := PV_OWNK_TowerCanon.Canon

theorem canon_iff (q : Q) : Canon q ↔ PV_OWNJ_DecodeFold.Canon q := by
 constructor
 · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩; exact ⟨a,b,c,d⟩
 · rintro ⟨a,b,c,d⟩; exact ⟨⟨a,b⟩,c,d⟩

/-- Concrete instance: no Decoder field remains a hypothesis. -/
theorem decoder : PV_OWNJ_DecodeFold.Decoder decode := by
 constructor
 · exact PV_OWNK_QMDecode.zero
 · exact PV_OWNK_QMDecode.one
 · exact (canon_iff _).mp PV_OWNK_TowerCanon.zero_canon
 · exact (canon_iff _).mp PV_OWNK_TowerCanon.one_canon
 · intro x y hx hy
   exact ⟨(canon_iff _).mp (PV_OWNK_TowerCanon.qm_add _ _
    ((canon_iff _).mpr hx) ((canon_iff _).mpr hy)),
    PV_OWNK_QMDecode.add _ _ ((canon_iff _).mpr hx) ((canon_iff _).mpr hy)⟩
 · intro x y hx hy
   exact ⟨(canon_iff _).mp (PV_OWNK_TowerCanon.qm_mul _ _),
    PV_OWNK_QMDecode.mul _ _ ((canon_iff _).mpr hx) ((canon_iff _).mpr hy)⟩
 · intro x hx
   refine ⟨(canon_iff _).mp (PV_OWNK_TowerCanon.qm_sub _ _
    PV_OWNK_TowerCanon.one_canon ((canon_iff _).mpr hx)),?_⟩
   have h := PV_OWNK_QMDecode.sub one x PV_OWNK_TowerCanon.one_canon ((canon_iff _).mpr hx)
   rw [PV_OWNK_QMDecode.one] at h
   exact h

theorem value_commutes (point column : List Q)
 (hp : ∀ q ∈ point, Canon q) (hc : ∀ q ∈ column, Canon q) :
 (PV_OWNI_RawConsumer.value point column (PV_OWNI_Scanner.width point)
  (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)).map decode =
 if column.length ≠ 1024 then none else some (PV_OWNJ_ValueBridge.sparse decode point column) :=
 PV_OWNJ_ValueBridge.value_commutes decode decoder point column
  (fun q h => (canon_iff _).mp (hp q h)) (fun q h => (canon_iff _).mp (hc q h))

/-- Complete value-phase Result, with exact scanner split and suffix. This
still concludes the ordered sparse value, not the unproved dense equation. -/
theorem source_commutes (point column : List Q) (hl : point.length = 10)
 (hp : ∀ q ∈ point, Canon q) (hc : ∀ q ∈ column, Canon q) :
 (do
  let value ← PV_OWNI_RawConsumer.source point column (PV_OWNI_Scanner.width point)
   (PV_OWNI_Scanner.trailing point) (PV_OWNI_Scanner.suffix point)
  ok (value.map decode)) =
 ok (if column.length ≠ 1024 then none else some (PV_OWNJ_ValueBridge.sparse decode point column)) := by
 rw [PV_OWNI_RawConsumer.result point column _ _ _
  (PV_OWNI_Scanner.split point hl) (PV_OWNI_Scanner.suffix_bound point)]
 simp only [bind_tc_ok]
 rw [value_commutes point column hp hc]
#print axioms canon_iff
#print axioms decoder
#print axioms value_commutes
#print axioms source_commutes
end R1Z.PV_OWNK_ConcreteDecoder

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNL_PrefixProduct
variable {K : Type} [Field K]
/-- The field step appearing in DecodeWeight, without changing its order. -/
def step (width pref : Nat) (acc : K × Nat) (coordinate : K) : K × Nat :=
 (acc.1 * (if pref.testBit (width-1-acc.2) then coordinate else 1-coordinate),acc.2+1)

def factors (width pref : Nat) : Nat → List K → List K
 | _,[] => []
 | index,x::xs =>
  (if pref.testBit (width-1-index) then x else 1-x) :: factors width pref (index+1) xs

theorem fold_product (width pref : Nat) (xs : List K) (acc : K) (index : Nat) :
 (xs.foldl (step width pref) (acc,index)).1 = acc * (factors width pref index xs).prod := by
 induction xs generalizing acc index with
 | nil => simp only [List.foldl_nil,factors,List.prod_nil,mul_one]
 | cons x xs ih =>
  simp only [List.foldl_cons,step]
  rw [ih]
  simp only [factors,List.prod_cons,mul_assoc]

open scoped BigOperators

theorem factors_product (width pref : Nat) (xs : List K) (index : Nat) :
 (factors width pref index xs).prod =
 ∏ i : Fin xs.length,
  if pref.testBit (width-1-(index+i.val)) then xs.get i else 1-xs.get i := by
 induction xs generalizing index with
 | nil => simp only [factors,List.prod_nil,List.length_nil,Fin.prod_univ_zero]
 | cons x xs ih =>
  simp only [factors,List.prod_cons,List.length_cons,Fin.prod_univ_succ,
   List.get_cons_zero,List.get_cons_succ',Fin.val_zero,Fin.val_succ,Nat.add_zero]
  rw [ih]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have h : index+1+i.val = index+(i.val+1) := by omega
  rw [h]

/-- Direct list fold to the usual Boolean-cube product; symbolic in width. -/
theorem prefix_weight (xs : List K) (pref : Fin (2^xs.length)) :
 (xs.foldl (step xs.length pref.val) (1,0)).1 =
 PV_OWNI_DensePrune.weight (fun i : Fin xs.length => xs.get i)
  (fun i => pref.val.testBit (xs.length-1-i.val)) := by
 rw [fold_product,factors_product,one_mul]
 simp only [PV_OWNI_DensePrune.weight,Nat.zero_add]
#print axioms fold_product
#print axioms factors_product
#print axioms prefix_weight
end R1Z.PV_OWNL_PrefixProduct

end
end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNM_FoldSum
open scoped BigOperators
open PV_OWNI_RawOps
variable {K : Type} [Field K]

theorem fold_sum {A : Type} (xs : List A) (f : A → K) (initial : K) :
 xs.foldl (fun sum x => sum+f x) initial = initial+(xs.map f).sum := by
 induction xs generalizing initial with
 | nil => simp only [List.foldl_nil,List.map_nil,List.sum_nil,add_zero]
 | cons x xs ih =>
  simp only [List.foldl_cons,List.map_cons,List.sum_cons,ih,add_assoc]

theorem range_sum (n : Nat) (f : Nat → K) :
 ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
 rw [← List.map_coe_finRange_eq_range]
 simp only [List.map_map]
 exact (Fin.sum_univ_def (fun i : Fin n => f i.val)).symm

/-- No column lookup is replaced by a different index; the source integer
range and ordered additive fold become precisely the finite row sum. -/
theorem sparse_sum (decode : Q → K) (point column : List Q) :
 PV_OWNJ_ValueBridge.sparse decode point column =
 ∑ a : Fin (2^PV_OWNI_Scanner.width point),
  decode (((point.take (PV_OWNI_Scanner.width point)).foldl
   (PV_OWNI_WeightTotal.step (PV_OWNI_Scanner.width point) a.val) (ops.one,0)).1) *
  decode (column[PV_RDB2D_SparseAddress.row a.val (PV_OWNI_Scanner.trailing point)
   (PV_OWNI_Scanner.suffix point)]?.getD zero) := by
 unfold PV_OWNJ_ValueBridge.sparse PV_OWNI_BuildTotal.entries
 rw [List.foldl_map]
 rw [fold_sum]
 simp only [zero_add]
 exact range_sum _ _

/-- The decoded concrete raw prefix fold is the finite prefix product. -/
theorem prefix_product (decode : Q → K) (D : PV_OWNJ_DecodeFold.Decoder decode)
 (point : List Q) (width pref : Nat)
 (hc : ∀ q ∈ point, PV_OWNJ_DecodeFold.Canon q) :
 decode (((point.take width).foldl (PV_OWNI_WeightTotal.step width pref) (ops.one,0)).1) =
 ∏ i : Fin ((point.take width).map decode).length,
  if pref.testBit (width-1-i.val) then ((point.take width).map decode).get i
  else 1-((point.take width).map decode).get i := by
 rw [one_value]
 have h := PV_OWNJ_DecodeWeight.weight decode D width pref (point.take width) (one,0)
  D.one_canon (fun q hq => hc q (List.mem_of_mem_take hq))
 have hh := congrArg (fun x : K × Nat => x.1) h.2
 simp only [D.one_eq] at hh
 rw [hh]
 change (((point.take width).map decode).foldl (PV_OWNL_PrefixProduct.step width pref) (1,0)).1 = _
 rw [PV_OWNL_PrefixProduct.fold_product,one_mul,PV_OWNL_PrefixProduct.factors_product]
 simp only [Nat.zero_add]

#print axioms fold_sum
#print axioms range_sum
#print axioms sparse_sum
#print axioms prefix_product
end R1Z.PV_OWNM_FoldSum

end
end

section
set_option autoImplicit false
namespace R1Z.PV_OWNL_Suffix
open PV_OWNI_RawOps PV_OWNI_Scanner

theorem head_bit (x : Q) (xs : List Q) :
 (bits (x::xs)).testBit xs.length = equal x one := by
 have hb := bits_bound xs
 cases h : equal x one <;>
  simp only [bits,h,Bool.false_eq_true,if_false,if_true,Nat.zero_mul,Nat.one_mul,
   Nat.zero_add,Nat.testBit_two_pow_add_eq,Nat.testBit_lt_two_pow hb,Bool.not_false]

theorem tail_bit (x : Q) (xs : List Q) (i : Nat) (hi : i < xs.length) :
 (bits (x::xs)).testBit i = (bits xs).testBit i := by
 have hr : bits (x::xs) % 2^xs.length = bits xs := by
  exact Nat.mul_add_mod_of_lt (bits_bound xs)
 have h := congrArg (fun n : Nat => n.testBit i) hr
 simpa only [Nat.testBit_mod_two_pow,show decide (i < xs.length) = true from by simp [hi],
  Bool.true_and] using h

theorem decoded_bits {K : Type} [Zero K] [One K] (decode : Q → K)
 (hz : decode zero = 0) (ho : decode one = 1) (xs : List Q)
 (hb : ∀ x ∈ xs, boolean x = true) (i : Fin xs.length) :
 decode (xs.get i) = if (bits xs).testBit (xs.length-1-i.val) then 1 else 0 := by
 induction xs with
 | nil => exact Fin.elim0 i
 | cons x xs ih =>
  refine Fin.cases ?_ (fun j => ?_) i
  · have hx := (PV_OWNJ_Rows.boolean_iff x).mp (hb x (by simp))
    simp only [List.get_cons_zero,List.length_cons,Fin.val_zero,Nat.sub_zero,
     Nat.add_sub_cancel,head_bit]
    rcases hx with rfl | rfl
    · rw [hz]
      have he : equal zero one = false := by
       apply Bool.eq_false_iff.mpr
       intro h
       have hv := congrArg (fun q : Q => q.c0.a.val) ((PV_OWNJ_Rows.equal_iff _ _).mp h)
       change 0 = 1 at hv
       omega
      rw [he];rfl
    · rw [ho,show equal one one = true from (PV_OWNJ_Rows.equal_iff _ _).mpr rfl]
      rfl
  · have ht := ih (fun y hy => hb y (List.mem_cons_of_mem _ hy)) j
    simpa only [List.get_cons_succ',List.length_cons,Fin.val_succ,
     show xs.length+1-1-(j.val+1) = xs.length-1-j.val from by omega,
     tail_bit x xs (xs.length-1-j.val) (by omega)] using ht

/-- Exactly the raw scanner suffix, with no equality-modulo-P substitution. -/
theorem scanner_decoded {K : Type} [Zero K] [One K] (decode : Q → K)
 (hz : decode zero = 0) (ho : decode one = 1) (point : List Q)
 (i : Fin (point.drop (width point)).length) :
 decode ((point.drop (width point)).get i) =
 if (suffix point).testBit ((point.drop (width point)).length-1-i.val) then 1 else 0 :=
 decoded_bits decode hz ho _ (PV_OWNJ_Rows.suffix_boolean point) i
#print axioms head_bit
#print axioms tail_bit
#print axioms decoded_bits
#print axioms scanner_decoded
end R1Z.PV_OWNL_Suffix

end

section
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNN_SourceDense
open scoped BigOperators
open Aeneas Aeneas.Std Result PV_OWNI_RawOps PV_OWNI_Scanner
open PV_OWNI_DensePrune PV_OWNL_RowEnumeration
variable {K : Type} [Field K]

theorem take_coordinates (decode : Q → K) (point : List Q) (w : Nat)
 (hw : w ≤ point.length) :
 (point.take w).map decode = List.ofFn (fun i : Fin w => decode (point[i.val]?.getD zero)) := by
 apply List.ext_getElem
 · simp only [List.length_map,List.length_take,List.length_ofFn,Nat.min_eq_left hw]
 · intro i hi hj
   have hb : i < point.length := by
    have hn : i<w := by simpa only [List.length_ofFn] using hj
    omega
   simp only [List.getElem_map,List.getElem_take,List.getElem_ofFn,
    List.getElem?_eq_getElem hb,Option.getD_some]

theorem prefix_weight (decode : Q → K) (D : PV_OWNJ_DecodeFold.Decoder decode)
 (point : List Q) (w : Nat) (hw : w ≤ point.length) (a : Fin (2^w))
 (hp : ∀ q ∈ point, PV_OWNJ_DecodeFold.Canon q) :
 decode (((point.take w).foldl (PV_OWNI_WeightTotal.step w a.val) (ops.one,0)).1) =
 weight (fun i : Fin w => decode (point[i.val]?.getD zero)) (tail w a) := by
 rw [one_value]
 have h := PV_OWNJ_DecodeWeight.weight decode D w a.val (point.take w) (one,0)
  D.one_canon (fun q hq => hp q (List.mem_of_mem_take hq))
 have hh := congrArg (fun x : K × Nat => x.1) h.2
 simp only [D.one_eq] at hh
 rw [hh,take_coordinates decode point w hw]
 change ((List.ofFn (fun i : Fin w => decode (point[i.val]?.getD zero))).foldl
  (PV_OWNL_PrefixProduct.step w a.val) (1,0)).1 = _
 have hprod := PV_OWNL_PrefixProduct.prefix_weight
  (List.ofFn (fun i : Fin w => decode (point[i.val]?.getD zero)))
  (⟨a.val,by simpa only [List.length_ofFn] using a.isLt⟩)
 simp only [List.length_ofFn,weight,tail,List.get_eq_getElem,List.getElem_ofFn] at hprod
 exact hprod.trans (Fin.prod_congr'
  (fun i : Fin w => if a.val.testBit (w-1-i.val) then decode (point[i.val]?.getD zero)
   else 1-decode (point[i.val]?.getD zero))
  (show (List.ofFn (fun i : Fin w => decode (point[i.val]?.getD zero))).length = w
   from List.length_ofFn))

/-- The scanner partitions the point into its non-Boolean prefix and Boolean suffix. -/
theorem scanner_suffix_length (point : List Q) :
 (point.drop (width point)).length = trailing point := by
 have hs := PV_RDB2D_SparseShape.split_length boolean point
 have hw : width point ≤ point.length := by
  unfold width PV_RDB2D_SparseShape.prefixLen
  omega
 simp only [List.length_drop]
 change width point + trailing point = point.length at hs
 omega

/-- Transport the suffix index before applying the dependent scanner theorem. -/
theorem scanner_decoded_cast (decode : Q → K)
 (D : PV_OWNJ_DecodeFold.Decoder decode) (point : List Q)
 (i : Fin (trailing point)) :
 decode ((point.drop (width point)).get
  (Fin.cast (scanner_suffix_length point).symm i)) =
 if (suffix point).testBit (trailing point-1-i.val) then 1 else 0 := by
 have h := PV_OWNL_Suffix.scanner_decoded decode D.zero_eq D.one_eq point
  (Fin.cast (scanner_suffix_length point).symm i)
 exact h.trans (congrArg (fun n => if (suffix point).testBit (n-1-i.val)
   then (1 : K) else 0) (scanner_suffix_length point))

theorem sparse_dense (decode : Q → K) (D : PV_OWNJ_DecodeFold.Decoder decode)
 (point column : List Q) (hl : point.length=10)
 (hp : ∀ q ∈ point, PV_OWNJ_DecodeFold.Canon q) :
 PV_OWNJ_ValueBridge.sparse decode point column = PV_OWNM_V239.dense decode zero point column := by
 let w := width point
 let t := trailing point
 have split : w+t=10 := PV_OWNI_Scanner.split point hl
 have hw : w ≤ point.length := by omega
 have htlen : (point.drop w).length = t := scanner_suffix_length point
 let suffix : Fin (2^t) := ⟨PV_OWNI_Scanner.suffix point,suffix_bound point⟩
 have hs : ∀ i : Fin t,
  decode (point[(Fin.natAdd w i).val]?.getD zero) = if tail t suffix i then 1 else 0 := by
  intro i
  have hd := scanner_decoded_cast decode D point i
  have hb : w+i.val < point.length := by omega
  change decode ((point.drop w).get (Fin.cast htlen.symm i)) =
   (if (PV_OWNI_Scanner.suffix point).testBit (t-1-i.val) then 1 else 0) at hd
  simp only [List.get_eq_getElem,List.getElem_drop,Fin.val_cast] at hd
  change decode (point[w+i.val]?.getD zero) =
   (if (PV_OWNI_Scanner.suffix point).testBit (t-1-i.val) then 1 else 0)
  rw [List.getElem?_eq_getElem hb,Option.getD_some]
  exact hd
 have hd := PV_OWNM_DenseRows.full_dense_sparse w t
  (fun i : Fin (w+t) => decode (point[i.val]?.getD zero)) suffix
  (fun r : Fin (2^(w+t)) => decode (column[r.val]?.getD zero)) hs
 have hf : PV_OWNM_DenseRows.fullDense (w+t)
  (fun i : Fin (w+t) => decode (point[i.val]?.getD zero))
  (fun r : Fin (2^(w+t)) => decode (column[r.val]?.getD zero)) =
  PV_OWNM_V239.dense decode zero point column := by
  rw [split]
  rfl
 rw [hf] at hd
 rw [hd,PV_OWNM_FoldSum.sparse_sum]
 apply Finset.sum_congr rfl
 intro a ha
 rw [prefix_weight decode D point w hw a hp]
 rfl

def source222 (point column : List Q) : Result (Option Q) :=
 PV_OWNI_RawConsumer.source point column (width point) (trailing point) (suffix point)

/-- Discharges the named scalar link for the complete raw source model. The
native association, input pipeline and byte-frame transcript links remain
separate obligations of restore; no dense value is assumed here. -/
theorem source_dense (decode : Q → K) (D : PV_OWNJ_DecodeFold.Decoder decode) :
 PV_OWNM_V239.PV_OWNM_Link_SourceDense decode zero source222 := by
 intro p c hl hp hc
 unfold source222
 rw [PV_OWNI_RawConsumer.result p c _ _ _ (PV_OWNI_Scanner.split p hl) (suffix_bound p)]
 simp only [bind_tc_ok]
 rw [PV_OWNJ_ValueBridge.value_commutes decode D p c hp hc]
 rw [sparse_dense decode D p c hl hp]

theorem concrete_source_dense :
 PV_OWNM_V239.PV_OWNM_Link_SourceDense PV_OWNK_ConcreteDecoder.decode zero source222 :=
 source_dense PV_OWNK_ConcreteDecoder.decode PV_OWNK_ConcreteDecoder.decoder

#print axioms concrete_source_dense
#print axioms take_coordinates
#print axioms prefix_weight
#print axioms scanner_suffix_length
#print axioms scanner_decoded_cast
#print axioms sparse_dense
#print axioms source_dense
open PV_OWNM_V239

/-- The scalar commutation hypothesis of the skeleton is discharged and consumed.
Actual-input, operational byte-frame and owned-source instances are still named
hypotheses, not silently supplied by independent model invariants. -/
theorem concrete_restore {W : Type}
 (wirePoints : List PV_OWNI_RawOps.Q → List (List PV_OWNI_RawOps.Q)) (isBoolean : PV_OWNI_RawOps.Q → Bool)
 (reconstruct879 reconstruct890 : Public → List PV_OWNI_RawOps.Q)
 (native : Input → List PV_OWNI_RawOps.Q → Nat → Execution PV_OWNK_ConcreteDecoder.K W)
 (resource : Input → List PV_OWNI_RawOps.Q → Nat → ResourceExit W)
 (failures : List Bool) (left right : Input)
 (inputL : PV_OWNM_Link_ActualInput wirePoints left)
 (inputR : PV_OWNM_Link_ActualInput wirePoints right)
 (cbL : PV_OWNM_Link_Transcript879 reconstruct879 left)
 (cbR : PV_OWNM_Link_Transcript879 reconstruct879 right)
 (finalL : PV_OWNM_Link_Transcript890 reconstruct890 left)
 (finalR : PV_OWNM_Link_Transcript890 reconstruct890 right)
 (ownedL : PV_OWNM_Link_OwnedPublicPlan PV_OWNK_ConcreteDecoder.decode PV_OWNN_SourceDense.source222
  wirePoints isBoolean native resource failures left)
 (ownedR : PV_OWNM_Link_OwnedPublicPlan PV_OWNK_ConcreteDecoder.decode PV_OWNN_SourceDense.source222
  wirePoints isBoolean native resource failures right)
 (samePublic : left.pubData = right.pubData) (sameSite : left.site = right.site)
 (sameLengths : left.columns.map List.length = right.columns.map List.length) :
 (∀ p ∈ wirePoints left.point, ∀ lane c, left.columns[lane]? = some c →
  native left p lane = attach (resource left p lane)
   (ok (if c.length ≠ 1024 then none else some (dense PV_OWNK_ConcreteDecoder.decode zero p c)))) ∧
 (∀ p ∈ wirePoints right.point, ∀ lane c, right.columns[lane]? = some c →
  native right p lane = attach (resource right p lane)
   (ok (if c.length ≠ 1024 then none else some (dense PV_OWNK_ConcreteDecoder.decode zero p c)))) ∧
 (∀ pL ∈ wirePoints left.point, ∀ pR ∈ wirePoints right.point,
  ∀ laneL laneR cL cR, left.columns[laneL]? = some cL →
  right.columns[laneR]? = some cR →
  (native left pL laneL).trace = (native right pR laneR).trace) :=
 PV_OWNM_V239.restore PV_OWNK_ConcreteDecoder.decode zero PV_OWNN_SourceDense.source222 wirePoints isBoolean
  reconstruct879 reconstruct890 native resource failures left right inputL inputR
  PV_OWNN_SourceDense.concrete_source_dense cbL cbR finalL finalR ownedL ownedR
  samePublic sameSite sameLengths

#print axioms concrete_restore
end R1Z.PV_OWNN_SourceDense

end
end

set_option autoImplicit false
noncomputable section
namespace PV_SKWC_OWNM
open R1Z R1Z.PV_OWNM_V239 Aeneas Aeneas.Std Result
abbrev K := PV_OWNK_ConcreteDecoder.K
abbrev decode := PV_OWNK_ConcreteDecoder.decode
abbrev zero := PV_OWNI_RawOps.zero
abbrev one := PV_OWNI_RawOps.one
abbrev source222 := PV_OWNN_SourceDense.source222
def point : List Q := List.replicate 10 one
def wirePoints (p : List Q) : List (List Q) := [p,p.reverse,p]
def columns : List (List Q) := [List.replicate 1024 one,List.replicate 1024 zero]
def input (site : Site) : Input := ⟨⟨[1],[[2]],1,2,3⟩,site,point,columns⟩
def reconstruct (_ : Public) : List Q := point
def resource (i : Input) (_ : List Q) (lane : Nat) : ResourceExit Nat :=
 .ready (lane+1) (plan PV_OWNI_Scanner.boolean (calls wirePoints i) [])
def native (i : Input) (p : List Q) (lane : Nat) : Execution K Nat :=
 attach (resource i p lane)
  (do let v ← source222 p (i.columns[lane]?.getD []); ok (v.map decode))
theorem actual_input (site : Site) : PV_OWNM_Link_ActualInput wirePoints (input site) := by
 have ho : Canon one := PV_OWNK_ConcreteDecoder.decoder.one_canon
 have hz : Canon zero := PV_OWNK_ConcreteDecoder.decoder.zero_canon
 constructor
 · exact List.length_replicate
 constructor
 · intro p hp
   simp only [wirePoints,List.mem_cons,List.not_mem_nil,or_false] at hp
   rcases hp with h|h|h <;> subst p <;>
    simp [input,point,List.mem_replicate,ho]
 · intro c hc q hq
   simp only [input,columns,List.mem_cons,List.not_mem_nil,or_false] at hc
   rcases hc with h|h <;> subst c
   · have h := (List.mem_replicate.mp hq).2; subst q; exact ho
   · have h := (List.mem_replicate.mp hq).2; subst q; exact hz

theorem owned (i : Input) :
 PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints PV_OWNI_Scanner.boolean
  native resource [] i := by
 constructor
 · intro p hp lane c hc
   simp only [native,hc,Option.getD_some]
 · intro p hp lane c hc
   rfl
/-- Concrete decoder and the proved scalar source law, on both sides and both sites.
Nonempty columns and wire points make every operational link active. -/
theorem satisfiable : ∃ pair : Input × Input,
 PV_OWNM_Link_ActualInput wirePoints pair.1 ∧
 PV_OWNM_Link_ActualInput wirePoints pair.2 ∧
 PV_OWNM_Link_SourceDense decode zero source222 ∧
 PV_OWNM_Link_Transcript879 reconstruct pair.1 ∧
 PV_OWNM_Link_Transcript879 reconstruct pair.2 ∧
 PV_OWNM_Link_Transcript890 reconstruct pair.1 ∧
 PV_OWNM_Link_Transcript890 reconstruct pair.2 ∧
 PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints PV_OWNI_Scanner.boolean native resource [] pair.1 ∧
 PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints PV_OWNI_Scanner.boolean native resource [] pair.2 ∧
 pair.1.pubData = pair.2.pubData ∧ pair.1.site = pair.2.site ∧
 pair.1.columns.map List.length = pair.2.columns.map List.length := by
 refine ⟨(input .callback879,input .callback879),actual_input _,actual_input _,
  PV_OWNN_SourceDense.concrete_source_dense,?_,?_,?_,?_,owned _,owned _,rfl,rfl,rfl⟩
 all_goals intro h; rfl
/-- Final-site transcript reconstruction is active as well. -/
theorem final_links : PV_OWNM_Link_ActualInput wirePoints (input .final890) ∧
 PV_OWNM_Link_Transcript879 reconstruct (input .final890) ∧
 PV_OWNM_Link_Transcript890 reconstruct (input .final890) ∧
 PV_OWNM_Link_OwnedPublicPlan decode source222 wirePoints PV_OWNI_Scanner.boolean native resource [] (input .final890) := by
 exact ⟨actual_input _,(fun _ => rfl),(fun _ => rfl),owned _⟩
theorem nondegenerate (site : Site) : (input site).point.length = 10 ∧
 (wirePoints (input site).point).length = 3 ∧
 ((input site).columns.map List.length) = [1024,1024] := by
 simp only [input, point, wirePoints, columns, List.map_cons, List.map_nil,
  List.length_replicate, List.length_cons, List.length_nil]
 exact ⟨True.intro, True.intro, True.intro⟩
#print axioms actual_input
#print axioms owned
#print axioms satisfiable
#print axioms final_links
#print axioms nondegenerate
end PV_SKWC_OWNM

