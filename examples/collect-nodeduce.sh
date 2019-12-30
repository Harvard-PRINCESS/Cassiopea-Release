#!/usr/bin/env bash
HOMEDIR=$(pwd)
RESULTDIR=$HOMEDIR/../bench
BENCHDIR=$HOMEDIR/../benchmark-results-$(git rev-parse --short HEAD)

mkdir -p $RESULTDIR

# collect benchmarks

# +acc +depend
SEEDS=5 FLAGS="--accumulation-operation" ./benchmark.sh "synth"
mv $BENCHDIR $RESULTDIR/no-deduce

# calculate average timings
cd $RESULTDIR/no-deduce
find . -name "synth-*.log" -print0 | sort -z | xargs -0 tail -n 1 | \
  $HOMEDIR/dump.py "synth" > ../no-deduce.csv
