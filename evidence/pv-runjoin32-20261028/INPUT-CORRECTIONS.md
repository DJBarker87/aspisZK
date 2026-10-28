# Retained input corrections

51300 launched one compiler and is charged as one rejected chunk. It stopped at
QueryScanExhaustion with `missing IR data file for module Init.Prelude`, exit1,
wall0.46s, RSS883290112bytes, swap0. No theorem or source-cohort failure is inferred.
The initial external overlay copied pinned .olean and olean companions but omitted
.ir files. Rule11 in local-lean.txt makes own-input correction authorized proof work.

The replacement environment adds5438 .ir companions from exactly the same pinned
external-object locations. external-ir-companions.json records each path/hash;
all5673 .olean hashes were checked again and remain unchanged. The same module
was isolated in51301 under that changed environment: exit0, wall1.54s,
RSS3407302656bytes, swap0. This is not an unchanged failed resubmission. The other
39 modules of the original chunk are attempted separately as51302.

Compile-free import preflight detected four `public import` statements missed by
the inherited plain-import parser. Resolution now includes those edges, yielding
1986 project modules, three more than the initial1983: QM31WordFormulas,
QM31WordResidues, QuadraticTowerOperations (all AspisV8R17). No unpinned imports.
The first40 modules and all selected source hashes are unchanged. Initial plan
is retained as build-plan-initial.json; updated plan records full public-import
edges before any affected chunk is launched. This changes source selection
bookkeeping, not the pinned sources or proved declarations.
