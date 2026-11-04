# Findings and failed attempts

1. K001 skipped the length-four hint assertion; fixed by K002, controlled by K003. No closure from K001.
2. Metadata leaves use arbitrary metadata but one-byte AccountInfo data carriers; count K010/K011 uses list lengths up to three, shorter than production. These are explicitly restricted local results. No claim that these fixtures establish every caller's domain.
3. B004 failed on an unclosed conditional; its printed sorryAx is an elaborator artifact from the failed proof, excluded. B005 repaired the proof and uses no axioms.
4. B006 combined import found generated root instance instDiscriminantErrorIsize collision. Own new extraction Types is repaired with an explicit prefix-owned discriminant instance, same constructor order and integers. B007 corrected the attempted field spelling after checking the actual Discriminant definition. Dependent own modules must be rebuilt against the repaired Types. No inherited module is edited.
5. Before Lean proof credit, fixed the nested import regex in the own wrapper to actually traverse imported sources and pin objects. Aeneas object closure is always pinned independently. Infrastructure and validation policy remain unchanged.
