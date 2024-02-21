GOAL= main-icfp24
SLIDES= slides-tyde23
TARGET_MODULES= STLC
TARGET_FILES= agdamacros.tex unicodeletters.tex $(addprefix $(PREFIX)/, $(addsuffix .tex, $(TARGET_MODULES)))
PREFIX= latex

ZIPFILES= README.md Makefile $(addsuffix .lagda, $(TARGET_MODULES))
ZIPGOAL= supplement-icfp24.zip

ARXIVGOAL= $(GOAL).zip

AGDATEX= ../../agdatex/agdatex.py

$(GOAL).pdf: $(GOAL).tex $(TARGET_FILES) $(PREFIX)/agda-generated.sty
	TEXINPUTS=$(PREFIX)/:$(TEXINPUTS) pdflatex --synctex=1 -interaction=nonstopmode $(GOAL)

$(PREFIX)/%.tex: %.lagda
	agda --latex --only-scope-checking $<

$(ZIPGOAL): $(ZIPFILES)
	zip $@ $^

$(ARXIVGOAL): $(GOAL).tex $(GOAL).bbl $(TARGET_FILES) acmart.cls agda.sty ACM-Reference-Format.bst
	zip $@ $^

$(SLIDES).pdf: $(SLIDES).tex $(TARGET_FILES)
	pdflatex  --synctex=1 -interaction=nonstopmode $(SLIDES)

.PHONY: all type-check clean
all: $(GOAL).pdf $(ZIPGOAL)

### agdatex

runagdatex:
	$(AGDATEX) -v -r ../src ../src/*.agda

### clean up

clean:
	$(RM) -f *.agdai

### type checking

type-check:
	for src in $(addsuffix .lagda, $(TARGET_MODULES)) ; do \
		echo '***' checking $$src ; \
		agda $$src; \
	done
