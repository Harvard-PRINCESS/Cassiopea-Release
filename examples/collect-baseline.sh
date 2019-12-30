#!/usr/bin/env bash
HOMEDIR=$(pwd)
RESULTDIR=$HOMEDIR/../bench
BENCHDIR=$HOMEDIR/../benchmark-results-$(git rev-parse --short HEAD)

mkdir -p $RESULTDIR

# collect benchmarks

# +acc +deduce +depend
SEEDS=5 FLAGS="--accumulation-operation" ./benchmark.sh "deduce"
mv $BENCHDIR $RESULTDIR/baseline

# calculate average timings
cd $RESULTDIR/baseline
find . -name "deduce-*.log" -print0 | sort -z | xargs -0 tail -n 1 | \
  $HOMEDIR/dump.py "deduce" > ../baseline.csv
