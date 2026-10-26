# Stage 2: installed schedule array callbacks

FIx_Builder proves ordered fromFn output meanings from the actual bounded
callback calls, including capture-state equality. FIx_Absorption.block_value
and callback_value interpret the installed three-way absorption branch;
FIx_AbsorptionArray.value gives every actual returned cell and canonicality.
FIx_InitialVariant.value interprets the installed variant tuple;
FIx_InitialArray.callback_value/value interpret the installed prepared initial
array. FIx_ArrayMeaning converts list output meanings to indexed arrays and
proves symbolic repeat values. These are coefficient-meaning predecessors,
not full semantic24 meaning or deployed premise removal.

Passing current sources:012 Builder,014 Absorption,016 AbsorptionArray,
017 InitialVariant,019 InitialArray,020 ArrayMeaning,021 ScheduleModel
(definitions only). All theorem audits contain only standard axioms.
011,013,015,018 failed locally within these new proofs; retained and excluded.
No timeouts/memory kills/unchanged reruns. One capped host scope per attempt;
exact source/deps/revision/exit/wall/RSS/swap/axioms fields in receipts.
