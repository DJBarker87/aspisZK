import S2W_ExtractionBoundary

/-! D188 child-internal site-event ports. Timestamps count ACTUAL trace
positions, including intervening source events; they are not Site.rank.
This module concerns schedule projection, not account or buffer projection. -/
set_option autoImplicit false
namespace AspisR1.S2W_SiteSchedule
open S2LeadInterface

inductive Event (E : Type) where
  | source (event : E)
  | site (s : Site)

structure FirstSegments (E : Type) where
  beforeBatch : List (Event E)
  beforeQuery : List (Event E)
  beforeSave : List (Event E)
  afterSave : List (Event E)
structure SecondSegments (E : Type) where
  beforeResume : List (Event E)
  beforeBatch : List (Event E)
  beforeQuery : List (Event E)
  beforeFinish : List (Event E)
  afterFinish : List (Event E)

def firstTrace {E : Type} (f : FirstSegments E) : List (Event E) :=
  f.beforeBatch ++ [.site .batch0] ++ f.beforeQuery ++ [.site .query0] ++
    f.beforeSave ++ [.site .save] ++ f.afterSave

def secondTrace {E : Type} (s : SecondSegments E) : List (Event E) :=
  s.beforeResume ++ [.site .resume] ++ s.beforeBatch ++ [.site .batch1] ++
    s.beforeQuery ++ [.site .query1] ++ s.beforeFinish ++ [.site .finish] ++ s.afterFinish

/-- First-entry CHILD exports the three reached source marks from THIS
invocation's instrumented trace. It makes no assertion about clocks, ranks,
other transactions, full caller observations or S2CallerFacts. -/
structure FirstEntrySiteConeJoin {E : Type} (source : List (Event E)) (f : FirstSegments E) : Prop where
  sourceTrace : source = firstTrace f
/-- Second-entry CHILD exports its four actual reached marks, independently. -/
structure SecondEntrySiteConeJoin {E : Type} (source : List (Event E)) (s : SecondSegments E) : Prop where
  sourceTrace : source = secondTrace s

/-- One source prefix, TX1 invocation, its child execution, the write/history
interval, TX2 invocation and its child execution. All intervening events are
retained. Prefix/interval are parent/runtime trace segments, not rank clocks. -/
def timeline {E : Type} (pre middle : List (Event E)) (f : FirstSegments E) (s : SecondSegments E) :
    List (Event E) := pre ++ [.site .tx1] ++ firstTrace f ++ middle ++ [.site .tx2] ++ secondTrace s

def before {E : Type} (pre middle : List (Event E)) (f : FirstSegments E) (s : SecondSegments E) :
    Site → List (Event E)
  | .tx1 => pre
  | .batch0 => pre ++ [.site .tx1] ++ f.beforeBatch
  | .query0 => pre ++ [.site .tx1] ++ f.beforeBatch ++ [.site .batch0] ++ f.beforeQuery
  | .save => pre ++ [.site .tx1] ++ f.beforeBatch ++ [.site .batch0] ++ f.beforeQuery ++
      [.site .query0] ++ f.beforeSave
  | .tx2 => pre ++ [.site .tx1] ++ firstTrace f ++ middle
  | .resume => pre ++ [.site .tx1] ++ firstTrace f ++ middle ++ [.site .tx2] ++ s.beforeResume
  | .batch1 => pre ++ [.site .tx1] ++ firstTrace f ++ middle ++ [.site .tx2] ++ s.beforeResume ++
      [.site .resume] ++ s.beforeBatch
  | .query1 => pre ++ [.site .tx1] ++ firstTrace f ++ middle ++ [.site .tx2] ++ s.beforeResume ++
      [.site .resume] ++ s.beforeBatch ++ [.site .batch1] ++ s.beforeQuery
  | .finish => pre ++ [.site .tx1] ++ firstTrace f ++ middle ++ [.site .tx2] ++ s.beforeResume ++
      [.site .resume] ++ s.beforeBatch ++ [.site .batch1] ++ s.beforeQuery ++ [.site .query1] ++ s.beforeFinish

def after {E : Type} (middle : List (Event E)) (f : FirstSegments E) (s : SecondSegments E) :
    Site → List (Event E)
  | .tx1 => firstTrace f ++ middle ++ [.site .tx2] ++ secondTrace s
  | .batch0 => f.beforeQuery ++ [.site .query0] ++ f.beforeSave ++ [.site .save] ++ f.afterSave ++
      middle ++ [.site .tx2] ++ secondTrace s
  | .query0 => f.beforeSave ++ [.site .save] ++ f.afterSave ++ middle ++ [.site .tx2] ++ secondTrace s
  | .save => f.afterSave ++ middle ++ [.site .tx2] ++ secondTrace s
  | .tx2 => secondTrace s
  | .resume => s.beforeBatch ++ [.site .batch1] ++ s.beforeQuery ++ [.site .query1] ++
      s.beforeFinish ++ [.site .finish] ++ s.afterFinish
  | .batch1 => s.beforeQuery ++ [.site .query1] ++ s.beforeFinish ++ [.site .finish] ++ s.afterFinish
  | .query1 => s.beforeFinish ++ [.site .finish] ++ s.afterFinish
  | .finish => s.afterFinish

def clock {E : Type} (pre middle : List (Event E)) (f : FirstSegments E) (s : SecondSegments E)
    (site : Site) : Nat := (before pre middle f s site).length

theorem located {E : Type} (pre middle : List (Event E)) (f : FirstSegments E) (s : SecondSegments E)
    (site : Site) : timeline pre middle f s = before pre middle f s site ++
      [.site site] ++ after middle f s site := by
  cases site <;> simp only [timeline,before,after,firstTrace,secondTrace,List.append_assoc,List.cons_append,List.nil_append]

theorem reached {E : Type} (pre middle : List (Event E)) (f : FirstSegments E) (s : SecondSegments E)
    (site : Site) : Event.site site ∈ timeline pre middle f s := by
  rw [located pre middle f s site]
  exact List.mem_append_left _ (List.mem_append_right _ (by simp))

theorem ordered {E : Type} (pre middle : List (Event E)) (f : FirstSegments E) (s : SecondSegments E)
    (a b : Site) (order : a.rank < b.rank) : clock pre middle f s a < clock pre middle f s b := by
  cases a <;> cases b <;>
    simp only [Site.rank,clock,before,firstTrace,List.length_append,List.length_cons,List.length_nil] at * <;>
    omega

/-- The source trace supplied by the TWO separate child hypotheses contains
all accepted-run sites. This derives the reachedPrefix and callOrder types
for its schedule projection, with clocks proved to be actual prefix lengths. -/
theorem source_schedule {E : Type} (pre middle firstSource secondSource : List (Event E))
    (f : FirstSegments E) (s : SecondSegments E)
    (first : FirstEntrySiteConeJoin firstSource f) (second : SecondEntrySiteConeJoin secondSource s) :
    let events := pre ++ [.site .tx1] ++ firstSource ++ middle ++ [.site .tx2] ++ secondSource
    (∀ a, Event.site a ∈ events) ∧
    (∀ a b, a.rank < b.rank → Event.site b ∈ events → Event.site a ∈ events) ∧
    (∀ a b, a.rank < b.rank → Event.site a ∈ events → Event.site b ∈ events →
      clock pre middle f s a < clock pre middle f s b) ∧
    (∀ a, events = before pre middle f s a ++ [.site a] ++ after middle f s a) := by
  dsimp only
  rw [first.sourceTrace,second.sourceTrace]
  exact ⟨reached pre middle f s,fun a _ _ _ => reached pre middle f s a,
    fun a b order _ _ => ordered pre middle f s a b order,located pre middle f s⟩

#print axioms located
#print axioms reached
#print axioms ordered
#print axioms source_schedule
#print FirstEntrySiteConeJoin
#print SecondEntrySiteConeJoin
end AspisR1.S2W_SiteSchedule
