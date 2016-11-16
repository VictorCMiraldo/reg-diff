DIRGUARD=@mkdir -p $(@D)

MAIN_NAME=report2016
REFERENCES_NAME=references
REFHOOK_NAME=references_ifl2016
LATEXMKOPTS=-pdf -f
TEXT_PARTS_SRC_ROOT=text
TEXT_PARTS_SRC_GENTEX=$(TEXT_PARTS_SRC_ROOT)

MAINTEX=$(TEXT_PARTS_SRC_ROOT)/$(MAIN_NAME).tex
MAINPDF=./$(MAIN_NAME).pdf
REFERENCES=./$(REFERENCES_NAME).bib
REFHOOK=text/$(REFHOOK_NAME).tex

COMPILER=pdflatex -etex

all: $(MAINPDF)

$(MAINPDF): code/reg-diff-compiled \
	$(MAINTEX) \
	$(TEXT_PARTS:%=$(TEXT_PARTS_SRC_GENTEX)/%.tex) \
	$(CODE_AGDA_STY)
	latexmk $(LATEXMKOPTS) $(MAINTEX)

$(TEXT_PARTS_SRC_GENTEX)/%.tex: $(TEXT_PARTS_SRC_GENTEX)/%.lhs
	lhs2TeX -o $@ $<

code/reg-diff-compiled:
	code/compileAgdaTex .. code/excerpts
	touch code/reg-diff-compiled

force:
	$(COMPILER) $(MAINTEX)

nosrctex:
	rm -f text/paper.tex

clean:
	rm -f *.log
	rm -f *.ptb
	rm -f *.aux
	rm -f *.toc
	rm -f *.blg
	rm -f *.bbl
	rm -f *.out
	rm -f *.fdb_latexmk
	rm -f *.fls

cleanall: clean nosrctex
	rm -f paper.pdf

.PHONY: clean all
