#!/usr/bin/env bash
HOMEDIR=$(pwd)
RESULTDIR=$HOMEDIR/../bench
BENCHDIR=$HOMEDIR/../benchmark-results-$(git rev-parse --short HEAD)

mkdir -p $RESULTDIR

# collect benchmarks

# +acc +deduce
SEEDS=1 FLAGS="--no-depend" ./benchmark.sh "deduce"
mv $BENCHDIR $RESULTDIR/no-depend

# calculate average timings
cd $RESULTDIR/no-depend
find . -name "deduce-*.log" -print0 | sort -z | xargs -0 tail -n 1 | \
  $HOMEDIR/dump.py "deduce" > ../no-depend.csv
