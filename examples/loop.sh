for i in `seq 1 200`; do
  rm -f synth-arm32.log synth-arm32.prog;
  CASPFLAGS="--seed=${i}0000 $1" bmake verify-synth-arm32;
  cp -n synth-arm32.log synth-arm32-$i.log;
  cp -n verify-synth-arm32.log verify-synth-arm32-$i.log;
done
