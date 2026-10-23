# Same tensor output and regular dot readback

The exact source Execution output now gives equality of its actual tensor output slice and subsequent actual dot input scratch slice. This uses existing owned Vec borrow/back definitions; it introduces no allocator content or preserved-prefix contract. The model/runtime primitive boundary remains explicit.

The focused target passed M4400/j1/H3GiB/Max4GiB/Swap0 with standard axioms. Three rejected frontend attempts are retained: dot projection syntax, explicit projection argument syntax, and dependent rewrite motive. The accepted proof uses namespace projections and congrArg rather than dependent rewrite; no statement/premise changed and no limit increase occurred.
