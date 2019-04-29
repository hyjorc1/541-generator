NAME = report
LATEX = pdflatex
BIBTEX = bibtex

# WARNING: Must run latex paper.tex one time before making bbl will work

all:
	$(LATEX) $(NAME).tex
	$(BIBTEX) $(NAME)
	$(LATEX) $(NAME).tex
	$(LATEX) $(NAME).tex

clean:
	rm -f *.bbl *.blg *.aux *.log *.dvi *~
