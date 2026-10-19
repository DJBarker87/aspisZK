# Authenticated wrapper composed with the checked adopted parser

PROVED: when the extracted `tx2_authenticated` wrapper is instantiated with the extracted adopted-format parser, wrapper success implies that same proof bytes parsed successfully as S2, the source variant tag is 2, the Parsed observer succeeded, and the common caller succeeded with the same public/proof/checkpoint/hash/observer arguments.

The earlier independent wrapper theorem left its parser boundary universally quantified. This composition instantiates it with the checked source parser. Nominal variants/errors from the two extraction cuts are mapped field-for-field; no caller or input is substituted. The full `tx2_common`, actual slice-operation backend, public statement/Fiat–Shamir experiment correspondence and whole R14 remain OPEN. In particular this does not yet discharge M9's public `htag` hypothesis.

Joint importing exposed the existing global `instDiscriminantErrorIsize` name collision. We reused the repository's prefix/public-preparation naming adapter pattern: expand the two parser discriminant attributes with the same constructor-order readers and uniquely qualified instance names. The checker reverses this adapter exactly and verifies that parser function and success-proof sources are unchanged. Those dependencies were compiled once in the changed type-owner environment; the old wrapper owner was reused.

Four focused NUC targets passed at -M4400 with 1 GiB high / 2 GiB max / zero swap. Printed proof axioms are standard. Exact compiler/import/source/object pins, commands, wall/RSS/swap and logs are included under the common focused packet schema. No binary, resource-option override, new axiom or production source edit is included.
