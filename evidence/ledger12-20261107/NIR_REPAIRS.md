# Own script repairs

NIR_prepare.py initially assumed every root manifest had a roots key; NIG uses groups. Fixed the parser to include every group member. No proof was launched by the failed preparation step; L001 independently compiled the already-written new module. Validation is stricter: the union includes all 7645 predecessor and new roots. No shared infrastructure changed.
