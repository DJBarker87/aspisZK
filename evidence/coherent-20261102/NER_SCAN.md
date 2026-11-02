# Stage B scan

NER_R010 indexed the exact transitive module closure of RPx_Deployed and
NDR_CombinedAudit (16,058 modules, 2,316,265 serialized declaration entries).
NER_R011 visited 47,898,346 type/value/inductive-constructor references in
those modules' own private tables. No imported axiom summaries were used.
Every module's recorded import list matched the frozen cohort index, and
all 16,057 historical NDR object hashes matched NDR_FINAL_COHORT_PINS.json.
The extra module is NDR_CombinedAudit itself. Exact tables, import lists,
object hashes and rows are committed as compressed, SHA-256 checked inputs.

Dangling modules (complete result of the table-universe scan):

- JFw_Validator: validate_record_fields_loop.body.match_3 (six occurrences).
- JFw_Record: parse_record.match_3 (six occurrences).
- JGx_SdkAfterValidationEq: stage2_owned.match_3 (six occurrences).

The fully qualified names and every parent declaration are in NER_SCAN.json.
The first two matchers belong to AspisR1RecordParser.Funs; the third belongs
to AdapterRwModel. The import-transitive affected set contains 1,387 modules.
NER_SCAN.json records its complete dependency order.

NER_ModuleTables.lean reads all .olean/.server/.private parts with Lean's
reader and includes opaque values. Its table-universe scan tests existence
in the declared-name union; it does not assert that a particular importer
exposes every name or that all references are well typed. NER_LoadedScan.lean
separately checks every module's own declarations against env.checked.get.
It retains missing-name errors and compares each import list to the cohort.

Controls: NER_Plant.lean writes a deliberately invalid test object with a
reference to NER_Plant.missing, and a matched body-corrected object. These
are fixtures, not accepted proofs or release inputs. NER_R014 reports exactly
the planted edge and no control edges. R015 reports a planted import-list
mismatch. R017 runs the loaded-environment scanner on 603 modules including
both fixtures: exactly the planted edge is reported (exit 1 is expected),
and the corrected body has zero dangling references. NER_tests.py checks
both scanners, three negative validator controls, input/archive hashes,
cohort object pins, receipt source snapshots, caps and reservations.

Full-cohort loaded-environment scan is **not complete**: R018 reached Lean's
-M7000 memory guard (exit 1, 6.338875 s, 10,268,592 KiB RSS, zero swaps).
R019 changed the loading shape by omitting elaborator-extension initialization
while retaining private kernel data. It also reached the same guard (exit 1,
4.683315 s, 9,987,408 KiB RSS, zero swaps). Both scopes had the unchanged
6G/8G/zero-swap cap. No larger-cap retry was made. The two agg16 allowances
remain reserved for final coherent aggregation and audit. The serialized scan
is complete; its loaded-environment strengthening remains a final-run gate.

Own scanner implementation failures are retained: R002/R004-R008 freed regions
while ModuleData references remained live (SIGSEGV); R009 used an unavailable
JSON API; R016 used a reserved identifier. R010/R011 use a function boundary
that releases all table references before freeing regions. These are scanner
source issues, not lead infrastructure failures. No authoritative object was
changed and no proved module was edited.
