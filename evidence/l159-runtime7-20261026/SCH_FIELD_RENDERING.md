# Fresh field inventory rendering

The new import context prints `true/false`, `some/none` and `algebraMap` where
some inherited field catalogs printed `Bool.true/Bool.false`,
`Option.some/Option.none` and `Algebra.algebraMap`. Line wrapping consequently
also differs. Raw fresh stdout is preserved exactly. The offline comparison
normalizes ONLY these five qualified/unqualified constructor/constant spellings
and whitespace, then requires full equality of each field block, including
all witnesses, guards and quantifiers. SCH_LEDGER_DELTA.json records the alias
map and every field family with rendering-only differences. No changed field
is excused by a theorem/record name or merely by a matching field count.
