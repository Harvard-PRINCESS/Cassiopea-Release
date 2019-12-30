#!/usr/bin/env bash
HOMEDIR=$(pwd)
RESULTDIR=$HOMEDIR/../bench
BENCHDIR=$HOMEDIR/../benchmark-results-$(git rev-parse --short HEAD)

mkdir -p $RESULTDIR

# collect benchmarks

# verification
SEEDS=10 ./benchmark.sh "verify-hand"
mv $BENCHDIR $RESULTDIR/verify

# calculate average timings
cd $RESULTDIR/verify
find . -name "verify-hand-*.log" -print0 | sort -z | xargs -0 tail -n 1 | \
  $HOMEDIR/dump.py "verify-hand" > ../verify.csv
