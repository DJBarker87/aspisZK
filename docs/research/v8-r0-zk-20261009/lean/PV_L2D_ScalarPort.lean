import PV_L2B_SourceWords
set_option autoImplicit false
namespace PV_L2D_ScalarPort

structure Draw (S W : Type) where
  word : UInt32
  after : S
  events : List W

inductive Event (W : Type) where
  | cap (retry : Nat) (running : Bool)
  | word (event : W)
  | accept (accepted : Bool)
  deriving DecidableEq, Repr

structure Sample (S W : Type) where
  value : Option Nat
  consumed : Nat
  after : S
  events : List (Event W)

variable {S W : Type}

def stream (next : S → Draw S W) : Nat → S → List UInt32
  | 0, _ => []
  | n+1, s => (next s).word :: stream next n (next s).after

def after (next : S → Draw S W) : Nat → S → S
  | 0, s => s
  | n+1, s => after next n (next s).after

/-- All next-word observations are retained outside Option, including the
sixteenth rejected word and the terminating false cap guard on exhaustion. -/
def sample (next : S → Draw S W) : Nat → Nat → S → Sample S W
  | 0, retry, s => ⟨none,0,s,[.cap retry false]⟩
  | n+1, retry, s =>
    let d := next s
    let candidate := PV_L2B_SourceWords.candidate d.word
    if candidate<2147483647 then
      ⟨some candidate,1,d.after,.cap retry true :: (d.events.map Event.word ++ [.accept true])⟩
    else
      let r := sample next n (retry+1) d.after
      ⟨r.value,r.consumed+1,r.after,
        .cap retry true :: (d.events.map Event.word ++ .accept false :: r.events)⟩

theorem complete_source (next : S → Draw S W) (n retry : Nat) (s : S) :
    ((sample next n retry s).consumed,(sample next n retry s).value) =
      PV_L2B_SourceWords.source n (stream next n s) := by
  induction n generalizing retry s with
  | zero => rfl
  | succ n ih =>
    by_cases h : PV_L2B_SourceWords.candidate (next s).word<2147483647
    · simp [sample,stream,PV_L2B_SourceWords.source,h]
    · have he := ih (retry+1) (next s).after
      have hc := congrArg Prod.fst he
      have hv := congrArg Prod.snd he
      change (sample next n (retry+1) (next s).after).consumed =
        (PV_L2B_SourceWords.source n (stream next n (next s).after)).1 at hc
      change (sample next n (retry+1) (next s).after).value =
        (PV_L2B_SourceWords.source n (stream next n (next s).after)).2 at hv
      simp [sample,stream,PV_L2B_SourceWords.source,h,hc,hv]
#print axioms complete_source

theorem consumed_bound (next : S → Draw S W) (n retry : Nat) (s : S) :
    (sample next n retry s).consumed≤n := by
  have h := congrArg Prod.fst (complete_source next n retry s)
  change (sample next n retry s).consumed =
    (PV_L2B_SourceWords.source n (stream next n s)).1 at h
  rw [h]
  exact PV_L2B_SourceWords.source_consumed_bound n _
#print axioms consumed_bound

theorem after_exact (next : S → Draw S W) (n retry : Nat) (s : S) :
    (sample next n retry s).after = after next (sample next n retry s).consumed s := by
  induction n generalizing retry s with
  | zero => rfl
  | succ n ih =>
    by_cases h : PV_L2B_SourceWords.candidate (next s).word<2147483647
    · simp [sample,h,after]
    · simpa only [sample,h,ite_false,after] using ih (retry+1) (next s).after
#print axioms after_exact

theorem failure_keeps_trace (next : S → Draw S W) (n retry : Nat) (s : S) :
    (sample next n retry s).events≠[] := by
  cases n with
  | zero => simp [sample]
  | succ n => simp only [sample];split <;> simp
#print axioms failure_keeps_trace

theorem stream_length (next : S → Draw S W) (n : Nat) (s : S) :
    (stream next n s).length=n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [stream,ih]
#print axioms stream_length
end PV_L2D_ScalarPort
