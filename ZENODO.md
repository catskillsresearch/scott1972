# Zenodo deposit

## Metadata: `.zenodo.json` is authoritative

| File | Role |
|------|------|
| **`.zenodo.json`** | **Primary.** Resource type, LOC subjects, keywords, creators, license, related IDs, version. |
| `CITATION.cff` | **Secondary.** GitHub “Cite this repository.” Zenodo prefers `.zenodo.json` when both exist. |

## Build

```bash
bash scripts/package_zenodo.sh                 # rebuild PDF, then zip
bash scripts/package_zenodo.sh --skip-pdf-build  # zip only (arxiv.pdf already current)
```

Output: `dist/scott1972-zenodo.zip`

## Upload

1. [zenodo.org/deposit/new](https://zenodo.org/deposit/new)
2. Upload `dist/scott1972-zenodo.zip`
3. Confirm autofilled metadata from `.zenodo.json`
4. Publish → copy DOI into `CITATION.cff` `preferred-citation.doi` if desired

## Citation (after upload)

```text
Ericson, L. W. (2026). A Lean 4 Formalization of Scott's Continuous Lattices
(1972) (Version 1.0.0) [Software]. Zenodo.
https://doi.org/10.5281/zenodo.XXXXXXX
```

Related: https://arxiv.org/abs/2606.30782 · https://github.com/catskillsresearch/scott1972
