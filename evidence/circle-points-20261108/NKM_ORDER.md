# NKM order

1. NGB006: square → add → try_inv; None gives SingularParameter; Some gives sub/product then double/product.
2. NGB004: run 006 first; propagate SingularParameter before testing c1; then ParameterInCm31Subfield or point.
3. NGB002: sample % 2 selects one of two parameters; 004 Result match preserves point or returns (1,0). Prove error unreachable for each parameter.
