import MultiproofConePhysicalNode
import MultiproofConePhysicalLive

set_option autoImplicit false
namespace AspisR1.MultiproofConePhysicalTrace
open Aeneas Aeneas.Std Result MultiproofConeRef
open MultiproofConeNodeDomain MultiproofConeNodeIteration MultiproofConeLevelIteration
open MultiproofConePhysicalDigest MultiproofConePhysicalNode MultiproofConePhysicalLive

structure Event where
  index : Nat
  left : Array U8 32#usize
  right : Array U8 32#usize
  digest : Array U8 32#usize

def Event.output (e : Event) : Entry := (e.index/2,e.digest)

def Event.Valid {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X) (e : Event) : Prop :=
  D.digest hash (parts e.left e.right)=ok e.digest

/-- A chronological witness for actual successful extracted rows. Each event
retains its child reads BEFORE the in-place write, and its actual hash result. -/
inductive Trace {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X) (physical : Slice U8) :
    reference.Scratch → Usize → Usize → reference.Scratch → List Event → Prop
  | done (s : reference.Scratch) (i w : Usize) (halt : i≥s.n) :
      Trace D hash physical s i w {s with n:=w} []
  | next (s : reference.Scratch) (i w ni nw cursor : Usize) (parent : U32)
      (left right digest : Array U8 32#usize) (after final : reference.Scratch) (es : List Event)
      (wb : w.val<16) (active : i.val<s.n.val) (nwval : nw.val=w.val+1)
      (input : Input physical s i left right ni cursor)
      (hashed : D.digest hash (parts left right)=ok digest)
      (parentval : parent.val=s.idx.val[i.val]!.val/2)
      (state : after={s with idx:=s.idx.set w parent,val:=s.val.set w digest,«at»:=cursor})
      (step : reference.binary_step D hash s physical i w=ok (.Next after ni nw))
      (rest : Trace D hash physical after ni nw final es) :
      Trace D hash physical s i w final
        ({index:=s.idx.val[i.val]!.val,left:=left,right:=right,digest:=digest}::es)

/-- Physical digest content is established by induction over the chronological
write witness. In particular, an index-order theorem alone is insufficient. -/
theorem prefix_exact {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (physical : Slice U8) (s final : reference.Scratch) (i w : Usize) (es : List Event)
    (trace : Trace D hash physical s i w final es) :
    view final 0 final.n.val=view s 0 w.val ++ es.map Event.output := by
  induction trace with
  | done s i w halt => simp [view,cell]
  | next s i w ni nw cursor parent left right digest after final es wb active nwval input hashed parentval state step rest ih =>
    rw [ih,state,nwval,write_prefix s w parent digest cursor wb]
    simp only [List.map_cons,Event.output,parentval,List.append_assoc,List.singleton_append]

/-- Every retained event is an actual digest equation of the reached callback. -/
theorem valid_events {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (physical : Slice U8) (s final : reference.Scratch) (i w : Usize) (es : List Event)
    (trace : Trace D hash physical s i w final es) : ∀ e∈es, e.Valid D hash := by
  induction trace with
  | done s i w halt => simp
  | next s i w ni nw cursor parent left right digest after final es wb active nwval input hashed parentval state step rest ih =>
    intro e mem
    rcases List.mem_cons.mp mem with rfl | mem
    · exact hashed
    · exact ih e mem

/-- Existence is proved from actual bounded extracted execution, rather than
assuming a trace or physical output relation in the source contract. -/
theorem rows_trace {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (fuel : Nat)
    (s : reference.Scratch) (i w : Usize) (domain : RowDomain physical s i w)
    (final : reference.Scratch)
    (success : rows (fun s i w => reference.binary_step D hash s physical i w) fuel s i w=ok (.Done final)) :
    ∃ es, Trace D hash physical s i w final es := by
  induction fuel generalizing s i w with
  | zero =>
    simp only [rows] at success
    split at success
    next halt => cases success;exact ⟨[],.done s i w halt⟩
    next => cases success
  | succ fuel ih =>
    simp only [rows] at success
    split at success
    next halt => cases success;exact ⟨[],.done s i w halt⟩
    next active =>
      have act : i.val<s.n.val := by scalar_tac
      obtain ⟨out,eq,observed⟩ := binary_observed D hash total physical s i w domain act
      rw [eq] at success
      simp only [bind_tc_ok] at success
      cases out with
      | Stop stopped => cases success
      | Next after ni nw =>
        obtain ⟨_,eq',progress⟩ := binary_step_progress D hash total physical s i w domain act
        rw [eq] at eq';cases eq'
        obtain ⟨es,trace⟩ := ih after ni nw progress.2.1 success
        obtain ⟨left,right,digest,parent,cursor,input,hashed,pv,nwv,state⟩ := observed
        refine ⟨_ ,.next s i w ni nw cursor parent left right digest after final es
          (by have := domain.2.1;have := domain.2.2.2.1;omega) act nwv input hashed pv state eq trace⟩

theorem level_trace {X : Type} (D : aspis_core.digest.Digest32 X) (hash : X)
    (total : HashTotal D hash) (physical : Slice U8) (s final : reference.Scratch)
    (domain : Domain physical s)
    (success : reference.level_rows D hash s physical 0#usize 0#usize=ok (.Done final)) :
    ∃ es, Trace D hash physical s 0#usize 0#usize final es ∧
      view final 0 final.n.val=es.map Event.output ∧ ∀ e∈es, e.Valid D hash := by
  have dom : RowDomain physical s 0#usize 0#usize := ⟨domain.1,domain.2.1,by simp,by simp,domain.2.2⟩
  rw [rows_eq_extracted D hash total physical s.n.val s _ _ dom (by simp)] at success
  obtain ⟨es,trace⟩ := rows_trace D hash total physical s.n.val s _ _ dom final success
  refine ⟨es,trace,?_,valid_events D hash physical s final _ _ es trace⟩
  simpa [view] using prefix_exact D hash physical s final 0#usize 0#usize es trace

#print axioms prefix_exact
#print axioms valid_events
#print axioms rows_trace
#print axioms level_trace
end AspisR1.MultiproofConePhysicalTrace
