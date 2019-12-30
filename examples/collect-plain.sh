#!/usr/bin/env bash
HOMEDIR=$(pwd)
RESULTDIR=$HOMEDIR/../bench
BENCHDIR=$HOMEDIR/../benchmark-results-$(git rev-parse --short HEAD)

mkdir -p $RESULTDIR

# collect benchmarks

# +depend
SEEDS=5 ./benchmark.sh "synth"
mv $BENCHDIR $RESULTDIR/plain

# calculate average timings
cd $RESULTDIR/plain
find . -name "synth-*.log" -print0 | sort -z | xargs -0 tail -n 1 | \
  $HOMEDIR/dump.py "synth" > ../plain.csv
