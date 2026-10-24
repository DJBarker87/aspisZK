import Port22ARENA_VecFrame
import Port22ARENA_WordBody
set_option autoImplicit false
-- Complete statements, definitions and full individual accepted-axiom audit.
#print Port22ARENA.initial
#print Port22ARENA.candidate
#print Port22ARENA.storeCursor
#print Port22ARENA.alloc
#print Port22ARENA.events
#print Port22ARENA.cut
#print Port22ARENA.readLE
#print Port22ARENA.Separated
#print Port22ARENA.stores
#print Port22ARENA.wordInitial
#print Port22ARENA.wordSaturatingSub
#print Port22ARENA.wordCandidate
#check @Port22ARENA.mask_word
#print axioms Port22ARENA.mask_word
#check @Port22ARENA.candidate_le
#print axioms Port22ARENA.candidate_le
#check @Port22ARENA.masked_aligned
#print axioms Port22ARENA.masked_aligned
#check @Port22ARENA.qm31_aligned
#print axioms Port22ARENA.qm31_aligned
#check @Port22ARENA.four_u64_aligned
#print axioms Port22ARENA.four_u64_aligned
#check @Port22ARENA.initial_upper
#print axioms Port22ARENA.initial_upper
#check @Port22ARENA.success_interval
#print axioms Port22ARENA.success_interval
#check @Port22ARENA.store_outside
#print axioms Port22ARENA.store_outside
#check @Port22ARENA.alloc_outside
#print axioms Port22ARENA.alloc_outside
#check @Port22ARENA.null_no_write
#print axioms Port22ARENA.null_no_write
#check @Port22ARENA.ok_exact_store
#print axioms Port22ARENA.ok_exact_store
#check @Port22ARENA.prefix_retained
#print axioms Port22ARENA.prefix_retained
#check @Port22ARENA.readLE_congr
#print axioms Port22ARENA.readLE_congr
#check @Port22ARENA.store_length_frame
#print axioms Port22ARENA.store_length_frame
#check @Port22ARENA.stores_length_frame
#print axioms Port22ARENA.stores_length_frame
#check @Port22ARENA.fresh_reserve_length
#print axioms Port22ARENA.fresh_reserve_length
#check @Port22ARENA.fresh_reserve_empty
#print axioms Port22ARENA.fresh_reserve_empty
#check @Port22ARENA.wrapping_mask
#print axioms Port22ARENA.wrapping_mask
#check @Port22ARENA.saturating_word
#print axioms Port22ARENA.saturating_word
#check @Port22ARENA.initial_word
#print axioms Port22ARENA.initial_word
#check @Port22ARENA.candidate_word
#print axioms Port22ARENA.candidate_word
