import ListConstructorAllocationM10
import BinTableWork

/-! Constructor counters for every branch of binary leaf/node table parsing.
Input keys are borrowed. Copies are charged at take/append/ofFn/map sites;
failed entries retain the complete executed-prefix count. -/
set_option autoImplicit false
namespace AspisR1.RecoveryParserAllocationM10
open BinMerkle32Path ListConstructorAllocationM10

def testCells {A : Type} : Nat → List A → Nat
  | 0, _ => 1
  | _+1, [] => 1
  | n+1, _::xs => testCells n xs+1

theorem test_work {A : Type} (n : Nat) (xs : List A) :
    testCells n xs ≤ (BinLeafBoundedLength.test n xs).2 := by
  induction n generalizing xs with
  | zero => cases xs <;> exact Nat.le_refl _
  | succ n ih =>
    cases xs with
    | nil => exact Nat.le_refl _
    | cons x xs => exact Nat.add_le_add_right (ih xs) 1

def leafCells (tag : Byte) (width : Nat) (input : List Byte) : Nat :=
  let p := BinLeafListWork.take width (BinLeafListWork.drop 2 input).1
  let s := BinLeafListWork.drop (2+width) input
  let cost := dropCells 2 input+takeCells width (BinLeafListWork.drop 2 input).1+
    dropCells (2+width) input+testCells width p.1
  if (BinLeafBoundedLength.test width p.1).1 = true then
    if (BinLeafBoundedLength.test 32 s.1).1 = true then
      cost+testCells 32 s.1+appendCells p.1+2+
        equalCells (0x10::tag::(BinLeafListWork.append p.1 s.1).1) input
    else cost+testCells 32 s.1
  else cost

theorem leaf_work (tag : Byte) (width : Nat) (input : List Byte) :
    leafCells tag width input ≤ (BinLeafListWork.parse tag width input).2 := by
  have hd := drop_work 2 input
  have hp := take_work width (BinLeafListWork.drop 2 input).1
  have hs := drop_work (2+width) input
  have ht := test_work width (BinLeafListWork.take width (BinLeafListWork.drop 2 input).1).1
  have hu := test_work 32 (BinLeafListWork.drop (2+width) input).1
  have ha := append_work (BinLeafListWork.take width (BinLeafListWork.drop 2 input).1).1
    (BinLeafListWork.drop (2+width) input).1
  have he := equal_work
    (0x10::tag::(BinLeafListWork.append
      (BinLeafListWork.take width (BinLeafListWork.drop 2 input).1).1
      (BinLeafListWork.drop (2+width) input).1).1) input
  unfold leafCells BinLeafListWork.parse
  dsimp only
  split
  · split <;> dsimp only <;> omega
  · omega

def getCells : List Byte → Nat → Nat
  | [], _ => 1
  | _::_, 0 => 1
  | _::xs, n+1 => getCells xs n+1

theorem get_work (xs : List Byte) (n : Nat) : getCells xs n ≤ (BinNodeListWork.get xs n).2 := by
  induction xs generalizing n with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    cases n with
    | zero => exact Nat.le_refl _
    | succ n => exact Nat.add_le_add_right (ih n) 1

def nodeReadCells (input : List Byte) : Nat :=
  ((List.ofFn (fun i : Fin 64 => getCells input (1+i.val))).sum)+128

theorem sum_mono {A : Type} (xs : List A) (f g : A → Nat) (h : ∀ x ∈ xs, f x ≤ g x) :
    (xs.map f).sum ≤ (xs.map g).sum := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    exact Nat.add_le_add (h x List.mem_cons_self)
      (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

theorem node_read_work (input : List Byte) : nodeReadCells input ≤ (BinNodeListWork.read input).2 := by
  have h := sum_mono (List.finRange 64)
    (fun i => getCells input (1+i.val))
    (fun i => (BinNodeListWork.get input (1+i.val)).2) (fun i _ => get_work _ _)
  simp only [nodeReadCells,BinNodeListWork.read,List.map_map,Function.comp_def,
    List.ofFn_eq_map]
  exact Nat.add_le_add_right h 128

def nodeCells (input : List Byte) : Nat :=
  nodeReadCells input+66+
    equalCells (nodeInput (BinNodeListWork.children (BinNodeListWork.read input).1)) input+3

theorem node_work (input : List Byte) : nodeCells input ≤ (BinNodeListWork.parse input).2 := by
  have hr := node_read_work input
  have he := equal_work (nodeInput (BinNodeListWork.children (BinNodeListWork.read input).1)) input
  change _+66+_+3 ≤ _+66+_+3
  omega

def tableCells (tag : Byte) (width : Nat) : BinMerkleRecordedLog.Log → Nat
  | [] => 1
  | (input,_)::rest => tableCells tag width rest+nodeCells input+leafCells tag width input+8

theorem table_work (tag : Byte) (width : Nat) (log : BinMerkleRecordedLog.Log) :
    tableCells tag width log ≤ (BinTableWork.tables tag width log).2 := by
  induction log with
  | nil => exact Nat.le_refl _
  | cons entry rest ih =>
    rcases entry with ⟨input,digest⟩
    have hn := node_work input
    have hl := leaf_work tag width input
    change _+_+_+8 ≤ _+_+_+32
    omega

#print axioms test_work
#print axioms leaf_work
#print axioms get_work
#print axioms sum_mono
#print axioms node_read_work
#print axioms node_work
#print axioms table_work
end AspisR1.RecoveryParserAllocationM10
