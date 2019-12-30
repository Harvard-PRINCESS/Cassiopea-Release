#!/usr/bin/env bash
seed=0
while true
do
  seed=$((seed+1))
  echo $seed
  ../../../cassiopeia ../../usecase_machines/arm32.casp -synth spec-arm32.spec --no-branch --no-unify --accumulation --seed $seed --whiten solver -sv --debug --dump-solver -o synth-arm32.prog -l synth-arm32.log
  if [ $? -eq 0 ]
  then
    echo "HIT"
    mv synth-arm32.prog synth-arm32-$seed.prog
    mv synth-arm32.log synth-arm32-$seed.log
  fi
done
