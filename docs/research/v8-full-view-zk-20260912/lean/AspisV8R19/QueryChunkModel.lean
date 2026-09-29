import AspisV8R19.QueryChunkExecution
import AspisV8R19.Q22WordScan

/-! Transport actual typed chunk execution to the retained q22 scan model.
Draw/count bounds justify counter arithmetic and vector growth. This does not
yet identify the outer block stream or prove the public argument guard. -/
set_option autoImplicit false
namespace AspisV8R19.QueryChunkModel
open Aeneas Aeneas.Std Result AspisR86Query QueryChunkExecution

def small64 (n : Nat) (h : n ≤ 64) : Usize :=
  UScalar.ofNatCore n (by have := Usize.cMax_bound; scalar_tac)

theorem small64_val (n : Nat) (h : n ≤ 64) : (small64 n h).val=n := rfl

theorem try_small64 (n : Nat) (h : n ≤ 64) :
    UScalar.tryMk .Usize n = .ok (small64 n h) := by
  have hb : UScalar.inBounds .Usize n := by have := Usize.cMax_bound; scalar_tac
  have hs := UScalar.tryMk_eq .Usize n
  cases he : UScalar.tryMk .Usize n with
  | fail e => simp only [he] at hs; exact False.elim (hs hb)
  | div => simp only [he] at hs
  | ok a =>
      simp only [he] at hs
      congr 1
      apply UScalar.eq_of_val_eq
      exact hs.1

def appendValue (out : Values) (x : U32) (h : out.val.length < 22) : Values :=
  ⟨out.val++[x],by have := Usize.cMax_bound; simp only [List.length_append,List.length_singleton]; scalar_tac⟩

theorem append_success (out : Values) (x : U32) (h : out.val.length < 22) :
    alloc.vec.Vec.push out x = .ok (appendValue out x h) := by
  have hb : out.val.length+1 ≤ U32.max := by scalar_tac
  simp [alloc.vec.Vec.push,appendValue,hb]

def view (out : Values) (draws : Usize) : Q22WordScan.ScanState :=
  ⟨out.val.map UScalar.val,draws.val⟩

def candidates (mask : U32) (ws : List Word) : List Nat :=
  ws.map (fun w => (core.num.U32.from_le_bytes w &&& mask).val)

theorem mem_val (out : Values) (x : U32) :
    x.val ∈ out.val.map UScalar.val ↔ x ∈ out.val := by
  constructor
  · intro h
    obtain ⟨y,hy,he⟩ := List.mem_map.mp h
    have heq : y=x := UScalar.eq_of_val_eq he
    simpa [heq] using hy
  · intro h; exact List.mem_map.mpr ⟨x,h,rfl⟩

theorem run_exact (mask : U32) (ws : List Word) (out : Values) (draws : Usize)
    (hc : out.val.length ≤ 22) (hd : draws.val ≤ 64) :
    ∃ out1 draws1, runWords mask ws out draws =
      .ok (out1,draws1,if (Q22WordScan.scan (view out draws) (candidates mask ws)).2 then 0#u32 else 1#u32) ∧
      view out1 draws1 = (Q22WordScan.scan (view out draws) (candidates mask ws)).1 := by
  induction ws generalizing out draws with
  | nil => exact ⟨out,draws,rfl,rfl⟩
  | cons word ws ih =>
      by_cases he : alloc.vec.Vec.len out = 22#usize
      · have hlen : out.val.length=22 := congrArg UScalar.val he
        refine ⟨out,draws,?_,?_⟩ <;>
          simp [runWords,candidates,Q22WordScan.scan,view,hlen]
      · have hlen : out.val.length < 22 := by
          have hn : out.val.length ≠ 22 := by
            intro h; apply he; apply UScalar.eq_of_val_eq; exact h
          omega
        by_cases he' : draws = 64#usize
        · refine ⟨out,draws,?_,?_⟩ <;>
            simp [runWords,he',candidates,Q22WordScan.scan,view]
        · have hdraw : draws.val < 64 := by
            have hn : draws.val ≠ 64 := by
              intro h; apply he'; apply UScalar.eq_of_val_eq; exact h
            omega
          let next := small64 (draws.val+1) (by omega)
          have hn : (draws+1#usize : Result Usize)=.ok next := try_small64 _ _
          let x := core.num.U32.from_le_bytes word &&& mask
          have hstop : ¬ ((out.val.map UScalar.val).length=22 ∨ draws.val=64) := by
            simp only [List.length_map]; omega
          by_cases hm : x ∈ out.val
          · obtain ⟨out1,draws1,hr,hv⟩ := ih out next hc (by dsimp only [next]; rw [small64_val]; omega)
            refine ⟨out1,draws1,?_,?_⟩
            · simp only [runWords,if_neg he,if_neg he',hn,bind_tc_ok,if_pos hm,
                candidates,List.map_cons,Q22WordScan.scan,if_neg hstop,Q22WordScan.keep,
                (mem_val out x).2 hm,if_true,view,next,small64_val,x] at hr ⊢
              convert hr using 1
              split_ifs <;> rfl
            · simpa only [candidates,List.map_cons,Q22WordScan.scan,if_neg hstop,Q22WordScan.keep,
                (mem_val out x).2 hm,if_true,view,next,small64_val,x] using hv
          · let more := appendValue out x hlen
            have hpush := append_success out x hlen
            obtain ⟨out1,draws1,hr,hv⟩ := ih more next
              (by dsimp [more,appendValue]; simp only [List.length_append,List.length_singleton]; omega)
              (by dsimp only [next]; rw [small64_val]; omega)
            have hmn : x.val ∉ out.val.map UScalar.val := fun h => hm ((mem_val out x).1 h)
            refine ⟨out1,draws1,?_,?_⟩
            · simpa only [runWords,if_neg he,if_neg he',hn,bind_tc_ok,if_neg hm,hpush,
                candidates,List.map_cons,Q22WordScan.scan,if_neg hstop,Q22WordScan.keep,
                if_neg hmn,view,next,small64_val,more,appendValue,List.map_append,List.map_singleton,List.map_nil,x] using hr
            · simpa only [candidates,List.map_cons,Q22WordScan.scan,if_neg hstop,Q22WordScan.keep,
                if_neg hmn,view,next,small64_val,more,appendValue,List.map_append,List.map_singleton,List.map_nil,x] using hv

#print axioms try_small64
#print axioms append_success
#print axioms mem_val
#print axioms run_exact
end AspisV8R19.QueryChunkModel
