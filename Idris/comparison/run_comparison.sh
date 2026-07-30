#!/usr/bin/env bash
#
# run_comparison.sh -- generate all data for the Parallel-Types vs Elysium
# (reviewer W2) comparison. Run this ON THE SERVER (28-core Xeon), from inside
# this comparison/ directory. Everything it needs is here (self-contained):
#   play2.erl        simple-distributor runtime (the one behind farm_*.txt / PT)
#   sk_profile.erl   timing shim (microseconds), same output as the originals
#   parMatMul.erl    Elysium task-farm MatMul     : run/2
#   parSumEuler2.erl Elysium task-farm SumEuler   : run_examples/2
#   parCpi.erl       Elysium task-farm CPI (NEW)  : run_examples/2
#   bench_seq.erl    shared SEQUENTIAL baselines  : run/3  (matmul|sumeuler|cpi)
#
# Output: results_<timestamp>/  with one farm_<bench>_<size>.txt per benchmark
# (same format as the existing farm_*.txt) plus seq_baselines.txt.
#
set -euo pipefail
cd "$(dirname "$0")"

# ------------------------- config (edit as needed) -------------------------
WORKERS="2 4 6 8 10 12 14 16 18 20 22 24 26 28"
REPS=10                  # farm reps per worker count (matches existing data)

MATMUL_SIZE=4000
SUMEULER_SIZE=40000
CPI_N=1000000000

RUN_CPI_FARM=1           # NEW / missing piece -- must run
RUN_MATMUL_FARM=0        # you already have farm_matmul_4000; set 1 to re-run
RUN_SUMEULER_FARM=0      # you already have farm_sumeuler_40000; set 1 to re-run

RUN_SEQ=1                # sequential baselines (Ts) via bench_seq
SEQ_REPS=3
SEQ_MATMUL=0             # MatMul 4000 seq is ~1.7 h/rep. Default off: the seq
                         #   code is byte-identical to PT's, so PT's Ts=6230 s
                         #   applies. Set 1 to re-measure on this machine.
# ---------------------------------------------------------------------------

# Guard: the runtime MUST use the simple distributor (send M whole). The broken
# Elysium Idris/play2.erl delegates to distributorS(Pid, M) element-wise.
if grep -qE 'distributorS\(Pid, *M\)' play2.erl; then
  echo "FATAL: play2.erl uses the element-wise distributor (distributorS)." >&2
  echo "       Replace it with the simple-distributor play2.erl before running." >&2
  exit 1
fi

OUT="results_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$OUT"
echo "compiling..."; erlc *.erl

# run_farm <module> <fun> <size> <label>
run_farm () {
  local mod=$1 fun=$2 size=$3 label=$4
  local f="$OUT/farm_${label}_${size}.txt"
  echo "# Elysium task farm: ${label} N=${size} -- $(date)" > "$f"
  echo ">>> ${label} farm (N=${size}, reps=${REPS})"
  for nw in $WORKERS; do
    echo "=== $nw workers ===" >> "$f"
    for ((i=0; i<REPS; i++)); do
      erl -noinput -pa . -eval "${mod}:${fun}(${nw}, ${size}), init:stop()." >> "$f" 2>&1
    done
    echo "    ${label} @ ${nw} workers done"
  done
  echo "    -> $f"
}

[ "$RUN_CPI_FARM"      = 1 ] && run_farm parCpi       run_examples "$CPI_N"       cpi
[ "$RUN_MATMUL_FARM"   = 1 ] && run_farm parMatMul    run          "$MATMUL_SIZE"  matmul
[ "$RUN_SUMEULER_FARM" = 1 ] && run_farm parSumEuler2 run_examples "$SUMEULER_SIZE" sumeuler

if [ "$RUN_SEQ" = 1 ]; then
  f="$OUT/seq_baselines.txt"
  echo "# shared sequential baselines (Ts) -- $(date)" > "$f"
  echo ">>> sequential baselines (reps=${SEQ_REPS})"
  erl -noinput -pa . -eval "bench_seq:run(sumeuler, ${SUMEULER_SIZE}, ${SEQ_REPS}), init:stop()." >> "$f" 2>&1
  erl -noinput -pa . -eval "bench_seq:run(cpi, ${CPI_N}, ${SEQ_REPS}), init:stop()." >> "$f" 2>&1
  if [ "$SEQ_MATMUL" = 1 ]; then
    erl -noinput -pa . -eval "bench_seq:run(matmul, ${MATMUL_SIZE}, ${SEQ_REPS}), init:stop()." >> "$f" 2>&1
  else
    echo "matmul ${MATMUL_SIZE}: skipped (SEQ_MATMUL=0); reuse PT Ts=6230 s (identical seq code)" >> "$f"
  fi
  echo "    -> $f"
fi

echo "DONE. Results in $(pwd)/$OUT/"
