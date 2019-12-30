#!/usr/bin/env bash
HOMEDIR=$(pwd)
RESULTDIR=$HOMEDIR/../bench
BENCHDIR=$HOMEDIR/../benchmark-results-$(git rev-parse --short HEAD)

mkdir -p $RESULTDIR

# collect benchmarks

# +deduce +depend
SEEDS=10 ./benchmark.sh "deduce"
mv $BENCHDIR $RESULTDIR/no-accumulation

# calculate average timings
cd $RESULTDIR/no-accumulation
find . -name "deduce-*.log" -print0 | sort -z | xargs -0 tail -n 1 | \
  $HOMEDIR/dump.py "deduce" > ../no-accumulation.csv
