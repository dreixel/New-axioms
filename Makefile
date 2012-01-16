PROJECT := CoSchemes
PROJECTSRC := $(PROJECT).lhs

LTX := $(wildcard *.lhs)
FMT := $(wildcard *.fmt)

all : color no-color

color : $(PROJECT).pdf

no-color: $(PROJECT)-nocolor.pdf

upperbound=4
LTX_OPTS=-halt-on-error

# The following target evaluates every top-level "test*" definition
test: $(PROJECT).hs
	@sh -c 'for test in `grep "test.* =" $< | sed "s/.*\(test.*\) =.*/\1/"`; do \
	  printf "Evaluating \"$$test\" : "; \
	  ghci -e $$test $< -fglasgow-exts; \
	done'

$(PROJECT).pdf : $(PROJECT).tex $(PROJECT).sty $(PROJECT).bib
	pdflatex $(LTX_OPTS) $(PROJECT).tex
	bibtex $(PROJECT)
	pdflatex $(PROJECT).tex

$(PROJECT).hs : $(LTX) $(PROJECT).fmt force
	lhs2TeX --newcode -shscode $(PROJECTSRC) > $@

ghcih : $(PROJECT).hs
	ghci -pgmL lhs2TeX -optL--pre -optL-sghchead $(PROJECT).lhs

lib : Appendix.lhs
	ghci -pgmL lhs2TeX -optL--pre Appendix.lhs

ghci : $(PROJECT).hs
	ghci -pgmL lhs2TeX -optL--pre $(PROJECT).lhs

$(PROJECT).tex : $(LTX) $(PROJECT).fmt force
	lhs2TeX --poly --set=color --set=draft $(PROJECTSRC) > $(PROJECT).tex

$(PROJECT)-nocolor.pdf : $(PROJECT)-nocolor.tex $(PROJECT).sty $(PROJECT).bib
	pdflatex $(LTX_OPTS) $(PROJECT)-nocolor.tex
	bibtex $(PROJECT)-nocolor
	sh -c 'i=0; \
	  while [ $$i -lt $(upperbound) ] && ( \
	       grep -c "Rerun" $(PROJECT)-nocolor.log \
	    || grep -c "undefined citations" $(PROJECT)-nocolor.log \
	    || grep -c "undefined references" $(PROJECT)-nocolor.log \
	    ); \
	  do pdflatex $(PROJECT)-nocolor.tex; \
	     i=`expr $$i + 1`;	\
	     done; \
	  echo "Iterations : $$i" \
	'

$(PROJECT)-nocolor.dvi : $(PROJECT)-nocolor.tex $(PROJECT).sty $(PROJECT).bib
	latex $(LTX_OPTS) $(PROJECT)-nocolor.tex
	bibtex $(PROJECT)-nocolor
	sh -c 'i=0; \
	  while [ $$i -lt $(upperbound) ] && ( \
	       grep -c "Rerun" $(PROJECT)-nocolor.log \
	    || grep -c "undefined citations" $(PROJECT)-nocolor.log \
	    || grep -c "undefined references" $(PROJECT)-nocolor.log \
	    ); \
	  do latex $(PROJECT)-nocolor.tex; \
	     i=`expr $$i + 1`;	\
	     done; \
	  echo "Iterations : $$i" \
	'

%.ps : %.dvi
	dvips -o $@ $<

$(PROJECT)-nocolor.tex : $(LTX) $(PROJECT).fmt force
	lhs2TeX --poly --set=draft $(PROJECTSRC) > $(PROJECT)-nocolor.tex

clean :
	rm -f *~ *.aux *.bbl *blg *.log *.ptb *.tex

clean-all : clean
	rm -f *.hs *.pdf

.PHONY : clean clean-all force

