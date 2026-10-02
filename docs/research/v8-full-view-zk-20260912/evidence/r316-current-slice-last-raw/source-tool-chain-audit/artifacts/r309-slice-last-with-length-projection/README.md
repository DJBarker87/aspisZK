# R309 Slice.last plus actual Slice.len language-item projection

R309 is a metadata-only projection of the original R294 LLBC, keeping the unchanged `Type[9]` (`core::option::Option`), `Fun[5]` (`core::slice::{Impl}::len`, `lang_item = slice_len_fn`), and `Fun[12]` (`core::slice::{Impl}::last`) rows. Their original ordered-declaration relative order is retained exactly: Type NonRec 9, Fun NonRec 5, Fun NonRec 12. Every declaration array keeps its original length and slot indices; all other declaration rows are null. `item_names` and `short_names` retain only these typed IDs.

`project_slice_last_with_len.py` generates the output and audits a full hash-cons decode/readback. It pins the R294 source, R298 typed-closure inventory, R274 reorder rules, and the schema-audited R220 serializer reference. It confirms all three decoded declaration rows are unchanged with no hash-cons cycle markers, all projected `Deduplicated` references resolve, retained hash-cons IDs/values are original, and every decoded metadata path is unchanged except the approved declaration rows, name maps, and `ordered_decls` filtering. Original array lengths are Type 63, Fun 243, Global 33, TraitDecl 32, TraitImpl 47; retained counts are Type 1, Fun 2, Global 0, TraitDecl 0, TraitImpl 0.

The source typed-AST edge remains Fun12 → Type9. Fun5 is recorded separately as the actual `slice_len_fn` lookup/call target used by the pinned Aeneas metadata prepass; this introduced prepass relation is not asserted as an original LLBC typed-AST edge. The exact prepass source copy and LLBC row/shape evidence are under `../r307-slice-metadata-inventory/`.

Input R294 SHA256: `bf5ea0b6f68ab17ef73d3e721c70c9193a0682d95dcbcaf693e93187cf71da6f`.
Output R309 SHA256: `9264aea58bf430b023ed8124bf8737ef6943e97230f08aa7982648f4f7557421`.
Hash-cons table: 422 original definitions; 19 definitions referenced in projected output; 403 unused definitions omitted.

This is only a projection candidate. No translation, build, or source-semantics claim is included here; translation is a separate authorized step.
