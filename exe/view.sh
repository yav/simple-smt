#!/bin/bash

# A simple script to view the diff of an sexpression
# This is intended to be used locally in a trusted environment

JSON_FILE=$(mktemp "exe/$1-XXXXXXXXXX")
cabal run -v0 diff-sexp < "$1" > "$JSON_FILE"
python3 -m http.server &
PID=$!
trap "kill $PID; rm '$JSON_FILE'" EXIT
sleep 1
open "http://localhost:8000/exe/see.html?file=$(basename $JSON_FILE)"
wait
