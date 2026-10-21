.PHONY: latex

latex:
	mkdir -p ../../.lake/latex/ULA ../../output/pdf
	latexmk -quiet -pdf -interaction=nonstopmode -halt-on-error -outdir=../../.lake/latex/ULA ULAupdate.tex
	cp ../../.lake/latex/ULA/ULAupdate.pdf ../../output/pdf/ULAupdate.pdf
