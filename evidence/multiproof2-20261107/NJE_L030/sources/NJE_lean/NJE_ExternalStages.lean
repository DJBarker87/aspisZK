import NJE_ExternalPacket
import NJE_SumStage

set_option autoImplicit false
noncomputable section
namespace NJE_ExternalStages
open Aeneas Aeneas.Std Result NJA_ChunkFrame NJE_ExternalBlocks

-- Reviewed projections of K071/K072 chunk writes, K073/K074 sum steps,
-- K075/K076 final-cell writes. Logs carry emitted replies at SAME arguments.
structure Cut (input : State U32) (bs : Nat → State U32)
    (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat)
    (steps : Nat → State U32) : Prop where
 block_start : bs 0=input
 block_cut : ∀ g : Fin 4,
   NJA_Mat4Cut.Cut (block (bs g.val) g)
     (NJE_Mat4Packet.events (block (bs g.val) g)) 4 (block (bs (g.val+1)) g)
 block_frame : ∀ (g : Fin 4) k, group k≠g → bs (g.val+1) k=bs g.val k
 sum_start : ∀ c, sums c 0=0
 sum_next : ∀ c (r : Fin 4), sums c (r.val+1)=sums c r.val+(bs 4 (pack r c)).val
 start : steps 0=bs 4
 arguments : ∀ i, args i=(steps i.val i).val+sums (column i) 4
 next : ∀ (n : Nat) (h : n<16), ∀ k,
   steps (n+1) k=if k=⟨n,h⟩ then NJE_Residue.word (args ⟨n,h⟩) else steps n k

theorem block_next (input : State U32) (bs : Nat → State U32)
    (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat) (steps : Nat → State U32)
    (cut : Cut input bs sums args steps) (g : Fin 4) :
    bs (g.val+1)=write (bs g.val) g (matrix (block (bs g.val) g)) := by
 have post : block (bs (g.val+1)) g=matrix (block (bs g.val) g) := by
   funext c
   exact (cut.block_cut g).2 c |>.2.2
 funext k
 by_cases same : group k=g
 · have eq := congrFun post (column k)
   simp only [block] at eq
   rw [←same,pack_parts] at eq
   simpa only [write,if_pos same,same] using eq
 · simpa only [write,if_neg same] using cut.block_frame g k same

theorem blocks_result (input : State U32) (bs : Nat → State U32)
    (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat) (steps : Nat → State U32)
    (cut : Cut input bs sums args steps) : bs 4=blocks input := by
 have all : ∀ (n : Nat), n≤4 → bs n=run input matrix n := by
   intro n hn
   induction n with
   | zero => exact cut.block_start
   | succ n ih =>
     have h : n<4 := by omega
     rw [block_next input bs sums args steps cut ⟨n,h⟩,run,dif_pos h,ih (by omega)]
 rw [all 4 (by omega),chronology]

theorem sum_result (input : State U32) (bs : Nat → State U32)
    (sums : Fin 4 → Nat → Nat) (args : Fin 16 → Nat) (steps : Nat → State U32)
    (cut : Cut input bs sums args steps) (c : Fin 4) :
    sums c 4=NJA_External.columnSum (blocks input) c := by
 have e3 := cut.sum_next c 3
 have e2 := cut.sum_next c 2
 have e1 := cut.sum_next c 1
 have e0 := cut.sum_next c 0
 change sums c 4=sums c 3+(bs 4 (pack 3 c)).val at e3
 change sums c 3=sums c 2+(bs 4 (pack 2 c)).val at e2
 change sums c 2=sums c 1+(bs 4 (pack 1 c)).val at e1
 change sums c 1=sums c 0+(bs 4 (pack 0 c)).val at e0
 rw [e3,e2,e1,e0,cut.sum_start c,blocks_result input bs sums args steps cut]
 rfl

#print block_next
#print axioms block_next
#print blocks_result
#print axioms blocks_result
#print sum_result
#print axioms sum_result
end NJE_ExternalStages
end
