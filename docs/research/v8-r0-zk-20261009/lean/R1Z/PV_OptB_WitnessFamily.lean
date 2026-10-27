import R1Z.BuilderCanonical
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OptB_WitnessFamily
open R0P AspisR1 AspisR1.SpendRelation R1Z.BuilderSpendRelation
variable {K : Type} [Field K] [DecidableEq K]

def path (w : Witness K) (t : Fin 16 → K) (level : Fin 24) : Bool × Digest K :=
  if h : 0 < level.val ∧ level.val ≤ 16 then
    (false,fun j => if j.val = 0 then t ⟨level.val-1,by omega⟩ else (w.path level).2 j)
  else w.path level

def witness (w : Witness K) (t : Fin 16 → K) : Witness K :=
  {w with path := path w t}

def root (pub : Public K) (w : Witness K) (t : Fin 16 → K) : Digest K :=
  merkleRoot (noteCommitment (ownerKey w.sk) (w.inputValue.val : K) pub.assetId w.salt) (path w t)

def publicInput (pub : Public K) (w : Witness K) (t : Fin 16 → K) : Public K :=
  {pub with anchor := root pub w t}

theorem path_zero (w : Witness K) (t : Fin 16 → K) : path w t 0 = w.path 0 := by
  unfold path
  exact dif_neg (by decide)

theorem path_coordinate (w : Witness K) (t : Fin 16 → K) (i : Fin 16) :
    (path w t ⟨i.val+1,by omega⟩).2 0 = t i := by
  have inside : 0 < i.val+1 ∧ i.val+1 ≤ 16 := by omega
  unfold path
  rw [dif_pos inside]
  change t ⟨i.val+1-1,_⟩ = t i
  rfl

theorem witness_injective (w : Witness K) : Function.Injective (witness w) := by
  intro t u same
  funext i
  have coordinates := congrArg (fun v : Witness K => (v.path ⟨i.val+1,by omega⟩).2 0) same
  change (path w t ⟨i.val+1,by omega⟩).2 0 = (path w u ⟨i.val+1,by omega⟩).2 0 at coordinates
  rw [path_coordinate,path_coordinate] at coordinates
  exact coordinates

theorem prefix_anchor_update (pub : Public K) (anchor leaf : Digest K) (n : Nat) :
    AppendPath.pathPrefix {pub with anchor := anchor} leaf n = AppendPath.pathPrefix pub leaf n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [AppendPath.pathPrefix]
    split_ifs with hn
    · rw [ih]
      rfl
    · exact ih

theorem rspend (pub : Public K) (w : Witness K) (valid : Rspend pub w) (t : Fin 16 → K) :
    Rspend (publicInput pub w t) (witness w t) := by
  refine ⟨valid.1,?_,valid.2.2.1,valid.2.2.2.1,valid.2.2.2.2.1,?_⟩
  · refine ⟨valid.2.1.valid,?_,?_,?_,valid.2.1.nullifier,rfl⟩
    · simpa only [witness,path_zero] using valid.2.1.spendable
    · simpa only [witness,path_zero,publicInput] using valid.2.1.commitment
    · simpa only [witness,path_zero] using valid.2.1.sibling
  · obtain ⟨pair,output,next,frontier⟩ := valid.2.2.2.2.2
    refine ⟨pair,output,?_,?_⟩
    · change pub.nextRoot = AppendPath.pathPrefix {pub with anchor := root pub w t} pair 20
      rw [prefix_anchor_update]
      exact next
    · intro hc
      change pub.nextFrontier ⟨digestCarry pub.nextPairIndex,hc⟩ =
        AppendPath.pathPrefix {pub with anchor := root pub w t} pair (digestCarry pub.nextPairIndex)
      rw [prefix_anchor_update]
      exact frontier hc

theorem rspendPlus [CharP K 2147483647] (pub : Public K) (w : Witness K)
    (valid : RspendPlus pub w) (t : Fin 16 → K) :
    RspendPlus (publicInput pub w t) (witness w t) :=
  ⟨rspend pub w valid.1 t,valid.2⟩

theorem public_eq_of_root_eq (pub : Public K) (w : Witness K) (t u : Fin 16 → K)
    (same : root pub w t = root pub w u) : publicInput pub w t = publicInput pub w u :=
  congrArg (fun anchor => {pub with anchor := anchor}) same

#print axioms path_zero
#print axioms path_coordinate
#print axioms witness_injective
#print axioms prefix_anchor_update
#print axioms rspend
#print axioms rspendPlus
#print axioms public_eq_of_root_eq
end R1Z.PV_OptB_WitnessFamily
