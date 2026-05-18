#!/usr/bin/env sh
# Build, then serve the bundle
cd "$(dirname "$0")/.." || exit 1
dune build @webapp/bundle && exec python3 -m http.server 8000 --directory _build/default/webapp/dist
