P=./venv/bin/python
sat() { $P "$@" 2>/dev/null | grep -q '^SAT'; }
exists() { local n=$1 k=$2 w=$3 m=$(($1-$2))
  [ $m -lt 1 ] && return 1
  sat pure.py $n $k $w && return 0
  if [ $n -ge 2 ]; then
    sat degens.py $n $k $w 1 one && return 0
    if [ $m -ge 2 ]; then
      sat degens.py $n $k $w 2 same && return 0
      [ $n -ge 3 ] && sat degens.py $n $k $w 2 chain && return 0
      [ $n -ge 4 ] && sat degens.py $n $k $w 2 disj && return 0
      for r in $(seq 3 $m); do sat degenr.py $n $k $w $r && return 0; done
    fi
  fi
  exists $((n-1)) $k $w }
for nk in "10 1" "10 2" "10 3" "11 1" "11 2" "10 4"; do
  set -- ${=nk}; res="inf"
  for w in 2 3 4 5 6 7 8; do if exists $1 $2 $w; then res=$w; break; fi; done
  echo "W_opt($1,$2,3) = $res"
done
