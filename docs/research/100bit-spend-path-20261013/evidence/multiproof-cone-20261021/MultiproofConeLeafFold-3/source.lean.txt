import MultiproofConeLeafContent
import MultiproofConeOpeningAdapters

set_option autoImplicit false
noncomputable section
namespace AspisR1.MultiproofConeLeafFold
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeLeafContent MultiproofConePhysicalViews
open MultiproofConePhysicalProgram
open OraclePortFrozenOrder OraclePortSelectedDraft OraclePortCompactDraft
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
attribute [local instance] Classical.propDecidable

def revLive (s : reference.Scratch) : Live := (live s 0 s.n.val).reverse

def push (i : Nat) (d : State) : Live → Option Live
  | [] => some [(i,d)]
  | (j,v)::tail => if i=j then if d=v then some ((j,v)::tail) else none
    else some ((i,d)::(j,v)::tail)

theorem decode_injective (a b : Digest) : decodeState a=decodeState b ↔ a=b := by
  constructor
  · intro eq
    simpa only [array_roundtrip] using congrArg encodeState eq
  · intro eq;rw [eq]

theorem insert_decode (i : Nat) (d : Digest) (rev : List MultiproofConePhysicalLive.Entry) :
    (MultiproofConeLeafContent.insert i d rev).map (List.map decodeEntry)=
      push i (decodeState d) (rev.map decodeEntry) := by
  cases rev with
  | nil => rfl
  | cons entry tail =>
    rcases entry with ⟨j,v⟩
    simp only [MultiproofConeLeafContent.insert,push,List.map_cons,decodeEntry]
    by_cases ij : i=j
    · simp only [ij,↓reduceIte,decode_injective]
      split <;> rfl
    · simp only [if_neg ij,Option.map_some,List.map_cons,decodeEntry]

theorem next_live (s : reference.Scratch) (i : U32) (d : Digest) (bound : s.n.val<16) :
    (next s i d bound).map revLive=push i.val (decodeState d) (revLive s) := by
  have eq := congrArg (Option.map (List.map decodeEntry)) (next_content s i d bound)
  rw [insert_decode] at eq
  unfold revLive live
  simpa only [Option.map_map,Function.comp_def,List.map_reverse] using eq

theorem next_bound (s : reference.Scratch) (i : U32) (d : Digest) (bound : s.n.val<16)
    (t : reference.Scratch) (eq : next s i d bound=some t) : t.n.val≤s.n.val+1 := by
  unfold next at eq
  split at eq
  · split at eq <;> cases eq
    omega
  · cases eq
    exact Nat.le_refl _

def key (q : Fin 22 → Fin 262144) (kind pos : Nat) : U32 :=
  UScalar.ofNat (index q kind pos) (by
    have b := (q ⟨pos%22,Nat.mod_lt _ (by decide)⟩).isLt
    unfold index
    dsimp only
    split <;> change _ ≤ 4294967295 <;> omega)

/-- Source-shaped leaf loop: every hash precedes its immediate physical
duplicate check, and no rejected suffix is requested. -/
def leaves (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat) :
    List Nat → reference.Scratch → Program Bytes State (Result (Option reference.Scratch))
  | [],s => .done (ok (some s))
  | pos::rest,s => .ask (leaf p kind pos) fun d =>
      match reference.leaf_step s (key q kind pos) (encodeState d) with
      | .fail e => .done (.fail e)
      | .div => .done .div
      | .ok none => .done (ok none)
      | .ok (some t) => leaves p q kind rest t

def model (p : Parsed) (q : Fin 22 → Fin 262144) (kind : Nat) :
    List Nat → Live → Program Bytes State (Option Live)
  | [],rev => .done (some rev)
  | pos::rest,rev => .ask (leaf p kind pos) fun d =>
      match push (index q kind pos) d rev with
      | none => .done none
      | some out => model p q kind rest out

theorem model_frozen (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (kind : Nat) (ps : List Nat) (rev : Live) :
    ((eval H (model p q kind ps rev)).1,
      (eval H (model p q kind ps rev)).2.map List.reverse) =
      eval H (hashLeaves p q kind ps rev) := by
  induction ps generalizing rev with
  | nil => rfl
  | cons pos rest ih =>
    cases rev with
    | nil =>
      simp only [model,push,hashLeaves,eval,Option.map_some]
      exact congrArg (fun x : List (Bytes × State) × Option Live =>
        ((leaf p kind pos,H (leaf p kind pos))::x.1,x.2))
        (ih [(index q kind pos,H (leaf p kind pos))])
    | cons entry tail =>
      rcases entry with ⟨j,v⟩
      by_cases ij : index q kind pos=j <;> by_cases dv : H (leaf p kind pos)=v <;>
        simp only [model,push,hashLeaves,eval,ij,dv,↓reduceIte,Option.map_none,Option.map_some] <;>
        first | rfl | simpa only [dv] using congrArg (fun x : List (Bytes × State) × Option Live => ((leaf p kind pos,H (leaf p kind pos))::x.1,x.2)) (ih _)

/-- Whole physical leaf/dedup induction. Only scratch capacity is required;
neither honest openings nor duplicate digest consistency is assumed. -/
theorem leaves_join (H : Bytes → State) (p : Parsed) (q : Fin 22 → Fin 262144)
    (kind : Nat) (ps : List Nat) (s : reference.Scratch)
    (room : s.n.val+ps.length≤16) :
    ∃ log out, eval H (leaves p q kind ps s)=(log,ok out) ∧
      eval H (model p q kind ps (revLive s))=(log,out.map revLive) ∧
      ∀ t, out=some t → t.n.val≤s.n.val+ps.length := by
  induction ps generalizing s with
  | nil => exact ⟨[],some s,rfl,rfl,by intro t eq;cases eq;omega⟩
  | cons pos rest ih =>
    have bound : s.n.val<16 := by simp only [List.length_cons] at room;omega
    have step := step_exact s (key q kind pos) (encodeState (H (leaf p kind pos))) bound
    have content := next_live s (key q kind pos) (encodeState (H (leaf p kind pos))) bound
    change (next s (key q kind pos) (encodeState (H (leaf p kind pos))) bound).map revLive =
      push (index q kind pos) (decodeState (encodeState (H (leaf p kind pos)))) (revLive s) at content
    rw [state_roundtrip] at content
    cases eq : next s (key q kind pos) (encodeState (H (leaf p kind pos))) bound with
    | none =>
      rw [eq] at step content
      simp only [Option.map_none] at content
      exact ⟨[(leaf p kind pos,H (leaf p kind pos))],none,
        by simp only [leaves,eval,step],by simp only [model,eval,← content,Option.map_none],by simp⟩
    | some t =>
      rw [eq] at step content
      simp only [Option.map_some] at content
      have tb := next_bound s (key q kind pos) (encodeState (H (leaf p kind pos))) bound t eq
      obtain ⟨log,out,source,target,final⟩ := ih t (by simp only [List.length_cons] at room;omega)
      refine ⟨(leaf p kind pos,H (leaf p kind pos))::log,out,?_,?_,?_⟩
      · simp only [leaves,eval,step,source]
      · simp only [model,eval,← content,target]
      · intro u eq;have ub := final u eq;simp only [List.length_cons];omega

#print axioms decode_injective
#print axioms insert_decode
#print axioms next_live
#print axioms next_bound
#print axioms model_frozen
#print axioms leaves_join
end AspisR1.MultiproofConeLeafFold
end
