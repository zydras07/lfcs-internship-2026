TEX := internship-report.tex
PDF := $(TEX:.tex=.pdf)

LATEX := pdflatex
LATEXFLAGS := -interaction=nonstopmode -halt-on-error -file-line-error -shell-escape

.PHONY: all build clean distclean view

all: build

build:
	$(LATEX) $(LATEXFLAGS) $(TEX)
	@if grep -q '\\bibliography{' $(TEX) 2>/dev/null || grep -q '\\addbibresource' $(TEX) 2>/dev/null; then \
	  bibtex $(basename $(TEX)); \
	fi
	$(LATEX) $(LATEXFLAGS) $(TEX)
	$(LATEX) $(LATEXFLAGS) $(TEX)

clean:
	rm -f *.aux *.log *.bbl *.blg *.toc *.out *.nav *.snm *.fls *.synctex.gz

distclean: clean
	rm -f $(PDF) *.pdf

view: build
	open $(PDF)

