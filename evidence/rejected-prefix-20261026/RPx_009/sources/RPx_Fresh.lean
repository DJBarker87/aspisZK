import RPx_RuntimePrefix
import AllAddressCollisionTrace
set_option autoImplicit false
noncomputable section
namespace AspisR1.RPx_Fresh
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps

def address (n : Nat) : Bytes := List.replicate n 0

theorem injective : Function.Injective address := by
  intro n m h
  have lengths := congrArg List.length h
  simpa only [address,List.length_replicate] using lengths

def reads : List Bytes → Program Bytes State Unit
  | [] => .done ()
  | a::as => .ask a (fun _=>reads as)

theorem evaluation (as : List Bytes) (H : Bytes → State) :
    eval H (reads as)=(as.map (fun a=>(a,H a)),()) := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [reads,eval,ih,List.map_cons]

def prelude (n : Nat) := reads ((List.range n).map address)

theorem occurrence_count (n : Nat) (H : Bytes → State) :
    (eval H (prelude n)).1.length=n := by
  rw [prelude,evaluation]
  simp only [List.length_map,List.length_range]

theorem first_read_count (n : Nat) (H : Bytes → State) :
    firstReads emptyTable (eval H (prelude n)).1=n := by
  rw [prelude,evaluation,AllAddressCollisionTrace.firstReads_eq_card_finiteSupport]
  simp only [List.map_map,Function.comp_def,Finset.filter_true_of_mem (fun _ _=>rfl)]
  have nodup : ((List.range n).map address).Nodup := (List.nodup_range n).map injective
  simpa only [List.length_map,List.length_range] using List.toFinset_card_of_nodup nodup

#print axioms injective
#print axioms evaluation
#print axioms occurrence_count
#print axioms first_read_count
end AspisR1.RPx_Fresh
end
