# Math Docs

## Environment

1. Install typst

```bash
brew install typst
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
