# Checkpoint composition indices

CPH_Top's actual persistence proof is CPH_Close -> CPG_History.on_cuts ->
CPR_DataWriter.on_cuts -> CPR_DataBinding.binding. SCJ_Checkpoint applies that
same proof and reindexes the copied payload to the saved bytes.
SCJ_NativeLoaded additionally derives the native cuts internally, then exports
the entry-buffer equality. Its ideal_cut composes that result with
SCE_SecondCutBytes.checkpoint for ANY source dictionary on exactly those entry
and saved-value indices. Thus different native/ideal dictionaries by themselves
are not an obstruction: physical-buffer association is sufficient.

Remaining composition question: the supplied game/native pair in Rc8 is fixed;
SCI's per-H source run chooses e1, then saved/post/final, then e2 adaptively.
The game needs to refer to those actual entries and saved value in each world.
This is a game-indexing/factory obligation, not a new RuntimePersistence item.
Neither game_does_not_select_second nor a dictionary mismatch establishes that
an actual-game-indexed accepted-run theorem is false. Only the generic sublist
event transport has been refuted.
