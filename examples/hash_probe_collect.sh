#!/bin/sh
# Rotated order per round; P core 2 and E core 16; one process per variant per round.
L="64 576 1024 1088 1089 1280 1536 1792 2047 2048 4096"
R="2047 1792 1536 1280 1089 1088 1024 576 64 4096 2048"
mkdir -p runs
for round in 1 2 3 4 5 6 7 8; do
  case $((round % 3)) in 0) o="tip tip-nopair tip-inline";; 1) o="tip-nopair tip-inline tip";; 2) o="tip-inline tip tip-nopair";; esac
  if [ $((round % 2)) = 0 ]; then lens=$R; else lens=$L; fi
  for cpu in 2 16; do for v in $o; do
    taskset -c $cpu ./probe-$v $lens > runs/$v-cpu$cpu-r$round.txt
  done; done
done
