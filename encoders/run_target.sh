#!/bin/zsh
# usage: run_target.sh n k w   -> reports SAT (with code) or UNSAT for "exists [[n,k,3]] with weight <= w"
cd /private/tmp/claude-501/-Users-yifanjing-Desktop-Princeton-AI-Scientist-trail1-solved/459d4a68-cb5d-4eda-a8cb-824b5813afeb/scratchpad
P=./venv/bin/python
try() { out=$($P "$@" 2>&1); echo "  [$*] $(echo "$out" | sed -n 2p)"; if echo "$out" | grep -q '^SAT'; then echo "$out" | tail -n +3; return 0; fi; return 1; }
exists() { local n=$1 k=$2 w=$3 m=$(($1-$2))
  [ $m -lt 1 ] && return 1
  try pure.py $n $k $w && return 0
  try degens.py $n $k $w 1 one && return 0
  if [ $m -ge 2 ]; then
    try degens.py $n $k $w 2 same && return 0
    try degens.py $n $k $w 2 chain && return 0
    try degens.py $n $k $w 2 disj && return 0
    for r in $(seq 3 $m); do try degenr.py $n $k $w $r && return 0; done
  fi
  exists $((n-1)) $k $w }
echo "=== target n=$1 k=$2 w=$3"
if exists $1 $2 $3; then echo "RESULT n=$1 k=$2 w=$3: EXISTS"; else echo "RESULT n=$1 k=$2 w=$3: NONE"; fi
