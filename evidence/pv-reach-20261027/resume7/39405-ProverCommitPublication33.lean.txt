import R1Z.ProverCommitTrustedStd24
/-! Publication loop denotations over the D145 map interface. No Rust caller
law is added to TrustedStd. Callbacks below are pure and can encode arbitrary
opening computations; the loop theorem does not prove those computations. -/
set_option autoImplicit false
namespace R1Z.ProverCommitPublication33
open ProverCommitTrustedStd24
variable {Key Value State Thread Slot Output Query : Type}
variable {cmp : Key → Key → Ordering} [Std.TransCmp cmp] [Std.LawfulEqCmp cmp]

def folded (map : MapAPI Key Value State cmp) (key : Query → Key)
    (make : Key → Value) : List Query → State → State × List Bool
  | [], s => (s, [])
  | q::qs, s =>
    let step := map.entry_or_insert_with s (key q) (fun _ => make (key q))
    let rest := folded map key make qs step.1
    (rest.1, step.2.2 :: rest.2)

/-- The shipped for-loop's left fold records callback calls in query order.
The recursive owner is over the remaining owned query list. -/
def foldedLoop (map : MapAPI Key Value State cmp) (key : Query → Key)
    (make : Key → Value) (qs : List Query) (s : State) : State × List Bool :=
  qs.foldl (fun acc q =>
    let step := map.entry_or_insert_with acc.1 (key q) (fun _ => make (key q))
    (step.1, acc.2 ++ [step.2.2])) (s, [])

theorem folded_loop_rec (map : MapAPI Key Value State cmp) (key : Query → Key)
    (make : Key → Value) (qs : List Query) (s : State) :
    foldedLoop map key make qs s = folded map key make qs s := by
  have aux : ∀ qs s log,
      qs.foldl (fun (acc : State × List Bool) q =>
        let step := map.entry_or_insert_with acc.1 (key q) (fun _ => make (key q))
        (step.1, acc.2 ++ [step.2.2])) (s,log) =
      ((folded map key make qs s).1, log ++ (folded map key make qs s).2) := by
    intro qs
    induction qs with
    | nil => intros; simp only [List.foldl_nil,folded,List.append_nil]
    | cons q qs ih =>
      intro s log
      simp only [List.foldl_cons,ih,folded,List.append_assoc,List.singleton_append]
  exact aux qs s []

variable [DecidableEq Thread]
variable (map : MapAPI Key Value State cmp) (tls : TLSAPI Thread Slot Output)
  (thread : Thread) (schedule : List (Thread × ProverCommitTLS23.Access Slot Output))
  (trusted : TrustedStd map tls thread schedule)
include trusted

/-- Universal duplicate/laziness transport uses precisely D145's one std field.
No bound on query count, table size, keys or values. -/
theorem folded_decode (key : Query → Key) (make : Key → Value)
    (qs : List Query) (s : State) :
    (map.decode (folded map key make qs s).1, (folded map key make qs s).2) =
      folded modelMap key make qs (map.decode s) := by
  induction qs generalizing s with
  | nil => rfl
  | cons q qs ih =>
    have step := trusted.btree_entry_or_insert_with s (key q) (fun _ => make (key q))
    have rest := ih (map.entry_or_insert_with s (key q) (fun _ => make (key q))).1
    cases found : (map.decode s)[key q]? with
    | none =>
      simp only [found] at step
      have hs := congrArg Prod.fst step
      have hc := congrArg (fun p => p.2.2) step
      simp only [Prod.fst, Prod.snd] at hs hc
      rw [hs] at rest
      simp only [folded,modelMap,found]
      rw [hc]
      exact congrArg (fun p => (p.1,true::p.2)) rest
    | some v =>
      simp only [found] at step
      have hs := congrArg Prod.fst step
      have hc := congrArg (fun p => p.2.2) step
      simp only [Prod.fst, Prod.snd] at hs hc
      rw [hs] at rest
      simp only [folded,modelMap,found]
      rw [hc]
      exact congrArg (fun p => (p.1,false::p.2)) rest

/-- Native-loop denotation, recursive reference and invocation trace coincide
through the named standard-library boundary. -/
theorem folded_loop_decode (key : Query → Key) (make : Key → Value)
    (qs : List Query) (s : State) :
    (map.decode (foldedLoop map key make qs s).1, (foldedLoop map key make qs s).2) =
      folded modelMap key make qs (map.decode s) := by
  rw [folded_loop_rec]
  exact folded_decode map tls thread schedule trusted key make qs s

/-- Iteration consumers get the exact sorted sequence, including its order.
This covers the order in which leaf-pair salts are requested; the actual
coin stream remains a separate source boundary. -/
theorem ordered_consumer {Acc : Type} (step : Acc → Key × Value → Acc)
    (s : State) (initial : Acc) :
    (map.entries s).foldl step initial = (map.decode s).toList.foldl step initial := by
  rw [trusted.btree_iter_ordered]

/-- Query publication repeats the lookup for every query, retaining repeats.
The result is a list of optional values so misses are not silently excluded. -/
theorem query_answers (key : Query → Key) (qs : List Query) (s : State) :
    qs.map (fun q => map.get s (key q)) =
      qs.map (fun q => (map.decode s)[key q]?) := by
  exact List.map_congr_left (fun _ _ => trusted.btree_get _ _)

#print axioms folded_loop_rec
#print axioms folded_decode
#print axioms folded_loop_decode
#print axioms ordered_consumer
#print axioms query_answers
end R1Z.ProverCommitPublication33
