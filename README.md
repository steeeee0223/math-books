# Math Docs

## Environment

1. Install typst

```bash
brew install typst
```

2. Install Lean with Elan

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"
lake exe cache get
```

Run the setup commands from the repository root. Elan reads `lean-toolchain`,
and `lake exe cache get` downloads the matching mathlib build cache.

## Lean

Check all Lean files in `alg-geo`:

```bash
pnpm -F @math-books/alg-geo lean
```

Check one Lean file from the repository root:

```bash
lake env lean books/alg-geo/src/sec-2-5/lean/exe.lean
```

## Initialize

1. Initialize with template

```bash
typst init @preview/ilm:1.4.1 <DIR>
```

2. VScode formatter settings

```json
// settings.json
{
  // ...
  "tinymist.formatterMode": "typstfmt",
  "[typst]": {
    "editor.defaultFormatter": "myriad-dreamin.tinymist",
    "editor.formatOnSave": true
  }
}
```
