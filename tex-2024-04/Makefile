GOAL= slides-gi24
TARGET_MODULES= STLC Tagless-final
TARGET_FILES= agdamacros.tex unicodeletters.tex $(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))
PREFIX= latex

AGDATEX= ../../agdatex/agdatex.py

$(GOAL).pdf: $(GOAL).tex $(TARGET_FILES) $(PREFIX)/agda-generated.sty
	TEXINPUTS=$(PREFIX)/:$(TEXINPUTS) pdflatex --synctex=1 -interaction=nonstopmode $(GOAL)
	bibtex $(GOAL)
	TEXINPUTS=$(PREFIX)/:$(TEXINPUTS) pdflatex --synctex=1 -interaction=nonstopmode $(GOAL)

$(PREFIX)/%.tex: %.lagda
	agda --latex --only-scope-checking $<

.PHONY: all type-check clean

all: $(GOAL).pdf 

### agdatex

runagdatex:
	$(AGDATEX) -v -r ../src ../src/StratF/*.agda ../src/StratF/Util/*.agda

### clean up

clean:
	$(RM) -f *.agdai

### type checking

type-check:
	for src in $(addsuffix .lagda, $(TARGET_MODULES)) ; do \
		echo '***' checking $$src ; \
		agda $$src; \
	done
