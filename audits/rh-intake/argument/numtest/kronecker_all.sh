#!/bin/sh
# Driver: every kronecker_run.py job used in NODE-NUMTEST2 (each < 5 min single-core; run 4 in parallel).
cd "$(dirname "$0")"
python3 -I kronecker_validate.py > out_kronecker_validate.txt
run() { python3 -I kronecker_run.py "$@" > /dev/null; }
run Zw 5 2000 40 & run Zi 7 2000 32 & run Zi 11 1600 40 & run Zw 11 1600 40 & wait
run Zi 19 1600 30 & run Zi 23 1600 30 & run Zw 17 1600 30 & run Zw 23 1600 30 & wait
run Zi 5 800 16 & run Zi 13 800 16 & run Zi 17 800 16 & run Zw 7 800 16 & wait
run Zw 13 800 16 & run Zw 19 800 16 & run C 5 700 16 & run C 7 700 16 & wait
run C 13 700 16 & run C 11 700 16 & run C 17 700 16 & run C 23 700 16 & wait
