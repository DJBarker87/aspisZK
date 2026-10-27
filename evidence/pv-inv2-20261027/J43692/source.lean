import R1Z.PV_Inv_MaskSource
set_option autoImplicit false
namespace R1Z.PV_Inv_MaskPartition
open R0P

def step (block : Fin 64) (acc : Nat) (r : Fin 1024) : Nat :=
  if r.val/16=block.val then acc ||| 2^(r.val%16) else acc

def maskOn (links : List CopyLink) (block : Fin 64) : Nat :=
  (links.flatMap (fun l => [l.producer.row,l.consumer.row])).foldl (step block) 0

theorem fold_initial (block : Fin 64) (rs : List (Fin 1024)) (initial : Nat) :
    rs.foldl (step block) initial = initial ||| rs.foldl (step block) 0 := by
  induction rs generalizing initial with
  | nil => simp
  | cons r rs ih =>
    simp only [List.foldl_cons]
    by_cases h : r.val/16=block.val
    · simp only [step,if_pos h,Nat.zero_or]
      rw [ih,ih]
      exact Nat.or_assoc _ _ _
    · simp only [step,if_neg h]
      exact ih initial

theorem append (xs ys : List CopyLink) (block : Fin 64) :
    maskOn (xs++ys) block = maskOn xs block ||| maskOn ys block := by
  unfold maskOn
  rw [List.flatMap_append,List.foldl_append,fold_initial]

theorem decomposition (block : Fin 64) :
    PV_Inv_MaskSource.mask block =
      maskOn PV_Inv_ActiveChunk00.links block |||
      maskOn PV_Inv_ActiveChunk01.links block |||
      maskOn PV_Inv_ActiveChunk02.links block |||
      maskOn PV_Inv_ActiveChunk03.links block |||
      maskOn PV_Inv_ActiveChunk04.links block |||
      maskOn PV_Inv_ActiveChunk05.links block |||
      maskOn PV_Inv_ActiveChunk06.links block |||
      maskOn PV_Inv_ActiveChunk07.links block |||
      maskOn PV_Inv_ActiveChunk08.links block |||
      maskOn PV_Inv_ActiveChunk09.links block |||
      maskOn PV_Inv_ActiveChunk10.links block |||
      maskOn PV_Inv_ActiveChunk11.links block |||
      maskOn PV_Inv_ActiveChunk12.links block |||
      maskOn PV_Inv_ActiveChunk13.links block |||
      maskOn PV_Inv_ActiveChunk14.links block |||
      maskOn PV_Inv_ActiveChunk15.links block |||
      maskOn PV_Inv_ActiveChunk16.links block |||
      maskOn PV_Inv_ActiveChunk17.links block |||
      maskOn PV_Inv_ActiveChunk18.links block |||
      maskOn PV_Inv_ActiveChunk19.links block |||
      maskOn PV_Inv_ActiveChunk20.links block |||
      maskOn PV_Inv_ActiveChunk21.links block |||
      maskOn PV_Inv_ActiveChunk22.links block |||
      maskOn PV_Inv_ActiveChunk23.links block |||
      maskOn PV_Inv_ActiveChunk24.links block |||
      maskOn PV_Inv_ActiveChunk25.links block |||
      maskOn PV_Inv_ActiveChunk26.links block |||
      maskOn PV_Inv_ActiveChunk27.links block |||
      maskOn PV_Inv_ActiveChunk28.links block |||
      maskOn PV_Inv_ActiveChunk29.links block |||
      maskOn PV_Inv_ActiveChunk30.links block |||
      maskOn PV_Inv_ActiveChunk31.links block |||
      maskOn PV_Inv_ActiveChunk32.links block |||
      maskOn PV_Inv_ActiveChunk33.links block := by
  change maskOn copyLinks block = _
  rw [←PV_Inv_ActiveRegistry.exact_table,PV_Inv_ActiveRegistry.chunks]
  simp only [append]

#print axioms fold_initial
#print axioms append
#print axioms decomposition
end R1Z.PV_Inv_MaskPartition
