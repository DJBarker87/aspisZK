# R43hc cyclic-carry evidence

The corrected R43 host, proof, SBF, and SVM artifacts and metadata are in this
directory. Host tensor control exited 0 (inner timed command: 30.15s wall,
536744 KB max RSS). Proof audit exited 0 (honest accepted and mutation rejected;
inner timed commands: 11.85s/454188 KB and 0.00s/3520 KB respectively).
The SBF build exited 0 (41.53s wall, 619124 KB max RSS). SVM exited 0 and
emitted six execution-failure observations; low-limit rows hit the CU meter,
while 100M diagnostics reached the OOM path. `bad-g-final` has no primary
acceptance marker before failure and is not a checked rejection.

Honest 100M parsed metrics: primary consumption 16,456,519 CU; G-tree
3,972,041; final FFT 3,040,361; G chord 2,051,371 (lead checkpoint metric);
ordinary 1,277,725. Full SVM process: 0.12s wall, 31668 KB max RSS, swap 0.
