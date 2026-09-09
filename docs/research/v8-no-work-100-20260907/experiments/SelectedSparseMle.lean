import SelectedSelectorExpansion

/-! Field-level source models of constraints_v4::sparse_eq_weights,
multilinear_evaluate_qm31 and the optimized v6_statement_points successor.
The Boolean suffix is derived, not supplied as a premise. Table values are
arbitrary; no honest trace, witness, residual correctness or decoder success
is assumed. Rust memory/limb execution and acceptance enforcement remain
separate from these list/field source algorithms. -/
set_option autoImplicit false
namespace AspisV8.SelectedSparseMle
open AspisV5ComponentCQM31TowerExact
open AspisV8.PositivePackBinding
open AspisV8.SelectedSelectorExpansion

variable {K : Type*} [CommRing K] [Nontrivial K] [DecidableEq K]

def isBoolean (x : K) : Bool := decide (x=0) || decide (x=1)
def suffixStep (acc : Nat) (x : K) : Nat :=
  (acc <<< 1) ||| (if x=1 then 1 else 0)
def bitStep (acc : Nat) (b : Bool) : Nat :=
  (acc <<< 1) ||| (if b then 1 else 0)
def decodeBits (bits : List Bool) : Nat := bits.foldl bitStep 0

/-- Literal reverse/take-while suffix scan and remaining-prefix enumeration.
The inner product uses the actual shift/and/zero test from the source. -/
def sparseWeights (point : List K) : List (Nat × K) :=
  let trailing := (point.reverse.takeWhile isBoolean).length
  let prefixLen := point.length-trailing
  let suffix := (point.drop prefixLen).foldl suffixStep 0
  (List.range (1 <<< prefixLen)).map (fun prefixIndex=>
    let row := (prefixIndex <<< trailing) ||| suffix
    let weight := ((point.take prefixLen).zipIdx).foldl (fun w item=>
      let x:=item.1
      let index:=item.2
      w*(if ((prefixIndex >>> (prefixLen-1-index)) &&& 1)=0 then 1-x else x)) 1
    (row,weight))

theorem isBoolean_bool (b : Bool) : isBoolean (boolValue (K:=K) b)=true := by
  cases b <;> simp [isBoolean,boolValue]

theorem suffixStep_bool (acc : Nat) (b : Bool) :
    suffixStep acc (boolValue (K:=K) b)=bitStep acc b := by
  cases b <;> simp [suffixStep,bitStep,boolValue]

theorem trailing_boolean_scan (bits : List Bool) :
    ((bits.map (boolValue (K:=K))).reverse.takeWhile isBoolean)=
      (bits.map (boolValue (K:=K))).reverse := by
  apply List.takeWhile_eq_self_iff.mpr
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hx)
  exact isBoolean_bool b

theorem suffix_boolean_decode (bits : List Bool) :
    (bits.map (boolValue (K:=K))).foldl suffixStep 0=decodeBits bits := by
  rw [List.foldl_map]
  unfold decodeBits
  congr 1
  funext acc b
  exact suffixStep_bool acc b

/-- An exact one-entry output, not a dense-sum identity which assumes that
the source's sparse helper happened to enumerate the correct support. -/
theorem sparseWeights_boolean (bits : List Bool) :
    sparseWeights (bits.map (boolValue (K:=K)))=[(decodeBits bits,1)] := by
  unfold sparseWeights
  rw [trailing_boolean_scan]
  simp only [List.length_reverse,List.length_map,Nat.sub_self,List.drop_zero,
    suffix_boolean_decode,List.take_zero,List.zipIdx_nil,List.foldl_nil]
  simp

theorem bitStep_arithmetic (acc : Nat) (b : Bool) :
    bitStep acc b=2*acc+(if b then 1 else 0) := by
  have hb : (if b then 1 else 0)<2^1 := by cases b <;> decide
  unfold bitStep
  rw [←Nat.shiftLeft_add_eq_or_of_lt hb acc,Nat.shiftLeft_eq]
  simp [Nat.mul_comm]

/-- Symbolic accumulation bound: no concrete 2^10-case row enumeration. -/
theorem decodeFold_bound (bits : List Bool) (acc k : Nat) (h : acc<2^k) :
    bits.foldl bitStep acc<2^(bits.length+k) := by
  induction bits generalizing acc k with
  | nil => simpa using h
  | cons b bits ih =>
    have hs : bitStep acc b<2^(k+1) := by
      rw [bitStep_arithmetic,pow_succ]
      cases b <;> simp only [Bool.false_eq_true,if_false,if_true] <;> omega
    have ht:=ih (bitStep acc b) (k+1) hs
    simpa only [List.foldl_cons,List.length_cons,Nat.add_assoc,
      Nat.add_comm 1 k] using ht

theorem decodeBits_bound (bits : List Bool) : decodeBits bits<2^bits.length := by
  simpa [decodeBits] using decodeFold_bound bits 0 0 (by decide)

/-- Models the exact selected length check and subsequent weighted reads.
getD merely totalizes the model; proved bounds below make its default inert
on every retained Boolean case. The actual point argument has length ten. -/
def sourceMle (column point : List K) : Option K :=
  if column.length=1024 then
    some ((sparseWeights point).foldl
      (fun acc item=>acc+item.2*column.getD item.1 0) 0)
  else none

theorem sourceMle_bad_length (column point : List K) (h : column.length≠1024) :
    sourceMle column point=none := by simp [sourceMle,h]

theorem sourceMle_boolean (column : List K) (bits : List Bool)
    (h : column.length=1024) :
    sourceMle column (bits.map boolValue)=some (column.getD (decodeBits bits) 0) := by
  rw [sourceMle,if_pos h,sparseWeights_boolean]
  simp

theorem boolean_read_bound (column : List K) (bits : List Bool)
    (hc : column.length=1024) (hb : bits.length=10) :
    decodeBits bits<column.length := by
  simpa [hc,hb] using decodeBits_bound bits

theorem sourceMle_boolean_checked (column : List K) (bits : List Bool)
    (hc : column.length=1024) (hb : bits.length=10) :
    sourceMle column (bits.map boolValue)=
      some (column[decodeBits bits]'(boolean_read_bound column bits hc hb)) := by
  rw [sourceMle_boolean _ _ hc,
    List.getD_eq_getElem _ _ (boolean_read_bound column bits hc hb)]

/-- Literal descending predecessor loop. The original bit is read from the
immutable point, not from the already-written output. -/
def successorStep (state : K × List K) (bit : K) : K × List K :=
  let both:=bit*state.1
  (both,(bit+state.1-(both+both))::state.2)

def sourceSuccessor (point : List K) : List K :=
  match point.reverse with
  | []=>[]
  | last::rest=>(rest.foldl successorStep (last,[1-last])).2

theorem zero_carry_loop (bits out : List K) :
    bits.foldl successorStep (0,out)=(0,bits.reverse++out) := by
  induction bits generalizing out with
  | nil => simp
  | cons b bits ih =>
    simp only [List.foldl_cons,successorStep,mul_zero,add_zero,zero_add,sub_zero]
    rw [ih]
    simp

/-- For every field-valued prefix, an even-index point ends in zero, so the
source's optimized last step turns it to one and leaves all prior bits alone. -/
theorem sourceSuccessor_last_zero (initial : List K) :
    sourceSuccessor (initial++[0])=initial++[1] := by
  simp only [sourceSuccessor,List.reverse_append,List.reverse_singleton,
    List.singleton_append,sub_zero,zero_carry_loop,List.reverse_reverse]

def currentBits : List Bool := List.ofFn (rowBits 1014)
def successorBits : List Bool := List.ofFn (rowBits 1015)
def commonPrefix : List Bool := [true,true,true,true,true,true,false,true,true]
def currentPoint : List K := currentBits.map boolValue
def nextPoint : List K := successorBits.map boolValue

/-- Only ten public bits are reduced; no field-valued recurrence is reduced. -/
theorem public_bit_inventory :
    currentBits=commonPrefix++[false] ∧ successorBits=commonPrefix++[true] ∧
    decodeBits currentBits=1014 ∧ decodeBits successorBits=1015 ∧
    currentBits.length=10 ∧ successorBits.length=10 := by decide

theorem sourceSuccessor_current : sourceSuccessor (currentPoint (K:=K))=nextPoint := by
  rcases public_bit_inventory with ⟨hc,hn,_,_,_,_⟩
  unfold currentPoint nextPoint
  rw [hc,hn,List.map_append,List.map_append]
  simpa [boolValue] using sourceSuccessor_last_zero (commonPrefix.map (boolValue (K:=K)))

theorem current_mle (column : List K) (h : column.length=1024) :
    sourceMle column currentPoint=some (column.getD 1014 0) := by
  rw [currentPoint,sourceMle_boolean _ _ h,public_bit_inventory.2.2.1]

theorem successor_mle (column : List K) (h : column.length=1024) :
    sourceMle column (sourceSuccessor currentPoint)=some (column.getD 1015 0) := by
  rw [sourceSuccessor_current,nextPoint,sourceMle_boolean _ _ h,
    public_bit_inventory.2.2.2.1]

theorem current_point_coordinate (i : Fin 10) :
    (currentPoint (K:=K)).getD i.val 0=booleanPoint (K:=K) 1014 i.val := by
  have hi : i.val<(currentPoint (K:=K)).length := by
    simpa only [currentPoint,currentBits,List.length_map,List.length_ofFn] using i.isLt
  rw [List.getD_eq_getElem _ _ hi]
  unfold currentPoint currentBits booleanPoint
  simp only [List.getElem_map,List.getElem_ofFn,rowBits]

/-- The source-shaped positive last pack now receives actual results of
the sparse MLE routine on the SAME arbitrary column tables. -/
def currentPositivePack (amount inverse : List QM31Exact) (publicAsset : QM31Exact) :
    Option QM31Exact := do
  let r←sourceMle amount currentPoint
  let c←sourceMle amount (sourceSuccessor currentPoint)
  let inv←sourceMle inverse currentPoint
  pure (expandedLastPack 1014 r publicAsset r c inv)

theorem current_positive_pack_binding (amount inverse : List QM31Exact)
    (publicAsset : QM31Exact) (ha : amount.length=1024) (hi : inverse.length=1024) :
    currentPositivePack amount inverse publicAsset=some 0 ↔
      amount.getD 1014 0*amount.getD 1015 0*inverse.getD 1014 0=1 := by
  simp only [currentPositivePack,current_mle _ ha,successor_mle _ ha,current_mle _ hi]
  change (some (expandedLastPack 1014 (amount.getD 1014 0) publicAsset
      (amount.getD 1014 0) (amount.getD 1015 0) (inverse.getD 1014 0))=some 0 ↔ _)
  rw [Option.some.injEq]
  exact expanded_row1014_pack_binding _ _ _ _ _

#print axioms trailing_boolean_scan
#print axioms suffix_boolean_decode
#print axioms sparseWeights_boolean
#print axioms decodeBits_bound
#print axioms sourceMle_bad_length
#print axioms sourceMle_boolean_checked
#print axioms zero_carry_loop
#print axioms sourceSuccessor_last_zero
#print axioms public_bit_inventory
#print axioms sourceSuccessor_current
#print axioms current_mle
#print axioms successor_mle
#print axioms current_point_coordinate
#print axioms current_positive_pack_binding
end AspisV8.SelectedSparseMle
