#!/usr/bin/env bash

# example FLAGS settings:
# --accumulation
# --no-unify
# --no-branch

# yon quick 'n' dirty benchmarking script
#
# pick what you want by editing the subdir makefiles,
# then run this from the examples directory
#
# sticks tons of copies of this directory into the benchmark-results directory,
# so watch out
#
# convenient command for glancing over all the times:
# find . -name "synth-*.out" -print0 | sort -z | xargs -0 tail -n 1 | less

# for mac user, `cp --parents` should be changed into `gcp -r --parents`

OUTDIR=../benchmark-results-$(git rev-parse --short HEAD)

# ten seeds by default
SEEDS=${SEEDS:-5}

mkdir -p $OUTDIR

for seed in `seq 1 1 ${SEEDS}`; do
  bmake clean ;
  CASPFLAGS="$FLAGS --seed $seed --whiten solver -sv" bmake $1 ;
  mkdir -p ${OUTDIR}/benchmark-${seed} ;
  find . \( -name "synth-*.prog" -o -name "*.out" -o -name "*.log" \) -exec \
    rsync -R {} ${OUTDIR}/benchmark-${seed} \; ;
done
