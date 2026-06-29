# Local PDF preview: LuaLaTeX handles UTF-8 Lean listings without pdfTeX memory limits.
# arXiv submission still uses pdfLaTeX (see scripts/package_arxiv_submit.sh).
$pdf_mode = 4;
$lualatex = 'lualatex -interaction=nonstopmode -halt-on-error %O %S';
