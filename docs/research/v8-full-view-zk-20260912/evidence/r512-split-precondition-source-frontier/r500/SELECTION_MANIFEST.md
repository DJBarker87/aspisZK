# R499 Fun32 exact closure selection

- Input: `R495ParserIteratorDependencies.llbc`, SHA-256
  `28ae0b878a54842a705ed71f4ab4fe374edc8b6530170d729bbce79945e1e24b`.
- Root: `Fun32`, `core::slice::<impl>::split_at_unchecked::precondition_check`.
- Output: `R499SplitAtPreconditionSelection.llbc`, SHA-256
  `aa06813bc1d0d30cd2f286174e4f2767ecb9625b6aee3aa6f678d723b6f107fd`.
- The output changes only `translated.ordered_decls`; the audit verified the
  surrounding prefix/suffix bytes and every other parsed JSON value are
  identical. Thus selected rows retain their original bodies and signatures.
- The closure contains exactly five ordered declarations: Fun32, foreign
  Fun33 `core::panicking::panic_nounwind_fmt`, Type15 `core::fmt::Arguments`,
  and Type16/Type17 `core::ptr::non_null::NonNull` instantiations. It contains
  no global, trait-declaration, or trait-implementation row; all 14 typed
  references resolve, and no ID-with-generics reference was unclassified.

The input capture includes `core::slice::_::split_at_unchecked` and
`core::num::_::unchecked_sub::precondition_check` in addition to its R494
parser includes. This is a declaration projection only. No translation,
execution, adequacy, or source-semantics claim follows from it.
