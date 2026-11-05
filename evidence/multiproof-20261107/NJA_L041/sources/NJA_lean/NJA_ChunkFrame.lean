import Aeneas

set_option autoImplicit false
namespace NJA_ChunkFrame
variable {α : Type}
abbrev State (α : Type) := Fin 16 → α

def pack (g c : Fin 4) : Fin 16 := ⟨4*g.val+c.val, by omega⟩
def group (i : Fin 16) : Fin 4 := ⟨i.val/4, by omega⟩
def column (i : Fin 16) : Fin 4 := ⟨i.val%4, by omega⟩
def block (s : State α) (g : Fin 4) : Fin 4 → α := fun c => s (pack g c)
def write (s : State α) (g : Fin 4) (v : Fin 4 → α) : State α :=
  fun i => if group i = g then v (column i) else s i

theorem group_pack (g c : Fin 4) : group (pack g c) = g := by
  apply Fin.ext
  simp only [group,pack]
  omega

theorem column_pack (g c : Fin 4) : column (pack g c) = c := by
  apply Fin.ext
  simp only [column,pack]
  omega

theorem pack_parts (i : Fin 16) : pack (group i) (column i) = i := by
  apply Fin.ext
  simp only [group,column,pack]
  omega

theorem same_block (s : State α) (g : Fin 4) (v : Fin 4 → α) : block (write s g v) g = v := by
  funext c
  simp [block,write,group_pack,column_pack]

theorem other_block (s : State α) (g h : Fin 4) (v : Fin 4 → α) (hne : h ≠ g) :
    block (write s g v) h = block s h := by
  funext c
  simp [block,write,group_pack,hne]

def processed (s : State α) (f : (Fin 4 → α) → Fin 4 → α) (n : Nat) : State α :=
  fun i => if (group i).val < n then f (block s (group i)) (column i) else s i

theorem current_block (s : State α) (f : (Fin 4 → α) → Fin 4 → α) (g : Fin 4) :
    block (processed s f g.val) g = block s g := by
  funext c
  simp [block,processed,group_pack]

theorem next_prefix (s : State α) (f : (Fin 4 → α) → Fin 4 → α) (g : Fin 4) :
    write (processed s f g.val) g (f (block (processed s f g.val) g)) = processed s f (g.val+1) := by
  rw [current_block]
  funext i
  by_cases same : group i = g
  · simp [write,processed,same]
  · have ne : (group i).val ≠ g.val := by intro eq; exact same (Fin.ext eq)
    have order : (group i).val < g.val+1 ↔ (group i).val < g.val := by omega
    simp [write,processed,same,order]

def run (s : State α) (f : (Fin 4 → α) → Fin 4 → α) : Nat → State α
  | 0 => s
  | n+1 => if h : n<4 then
      write (run s f n) ⟨n,h⟩ (f (block (run s f n) ⟨n,h⟩))
    else run s f n

theorem run_prefix (s : State α) (f : (Fin 4 → α) → Fin 4 → α) (n : Nat) (hn : n ≤ 4) :
    run s f n = processed s f n := by
  induction n with
  | zero => funext i; simp [run,processed]
  | succ n ih =>
    have h : n < 4 := by omega
    rw [run, dif_pos h, ih (by omega)]
    exact next_prefix s f ⟨n,h⟩

theorem complete (s : State α) (f : (Fin 4 → α) → Fin 4 → α) :
    run s f 4 = fun i => f (block s (group i)) (column i) := by
  rw [run_prefix s f 4 (by decide)]
  funext i
  simp [processed,(group i).isLt]

#print axioms group_pack
#print axioms column_pack
#print axioms pack_parts
#print axioms same_block
#print axioms other_block
#print axioms current_block
#print axioms next_prefix
#print axioms run_prefix
#print axioms complete
end NJA_ChunkFrame
