# R42c2 cyclic evidence

The corrected R42 SBF/SVM artifacts and metadata are in this directory. The
SBF build exited 0 (inner timed command: 56.19s wall, 619864 KB max RSS).
The SVM process exited 0 and emitted six execution-failure observations: four
low-limit 1.2M/1.4M CU failures and two 100M diagnostic failures. The honest
100M row emitted `primary-terminal-accepted` and then failed; `bad-g-final`
did not provide a checked rejection before failure.

For the honest 100M row, parsed remaining-CU markers give: primary
consumption 16,704,410; G-tree 3,972,041; final FFT 3,040,361; chord
2,258,151; compact ordinary 1,318,836. Full SVM process: 0.12s wall,
31704 KB max RSS, swap 0.
