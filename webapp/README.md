# Linden regex explorer

## Prerequisites

- `opam install warblre-engines.js` from Warblre
- `npm install` in `webapp/`

## Build (from repo root)

```sh
dune build @webapp/bundle # dev (unminified)
dune build --profile release @webapp/bundle # release
# ⇒ _build/default/webapp/dist/
```

Serve to http://localhost:8000 with `./webapp/serve.sh`.
