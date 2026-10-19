# Legacy native-gate fixture failure

The retained `candidate-native-gate-b` attempt exited 101 after its optimized example reported `honest acceptance: Parse`. The root review identified that attempt's retained fixture/profile as R1P2COST while the current terminal path uses R1P3COST. This is recorded as an incompatible historical fixture result; it is not candidate behavior evidence and was not repaired by weakening parsing. The current four-case measurements instead use individually pinned, retained P3 proof/ASF8 pairs with the current R18 harness.
